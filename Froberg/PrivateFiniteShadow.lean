import Froberg.PrivateGoodTargets
import Froberg.PrivateShadowBookkeeping
import Froberg.OuterCapacityBounds

/-! The complete finite regular/private split of the ideal outer shadow. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module MonomialExpansion OuterInjection AttachedMultiplication
variable {K : Type*} [Field K] {a z s k b h : ℕ}

def privateSourceEmbedding (hs : 0 < s) (ι : Fin b ↪ Fin z) : Fin b ↪ Degree (a+z) s where
  toFun i := ⟨privateExponent a s ι i,mem_exponents.mpr (privateExponent_degree ι i)⟩
  inj' := by
    intro i j he
    exact privateExponent_injective hs ι (congrArg Subtype.val he)

abbrev fiberCapacity (ι : Fin b ↪ Fin z) (v : Labels k a s → Fin h → K)
    (w : Fin b → Fin h → K) (β : Fin (a+z) →₀ ℕ) : ℕ :=
  finrank K ((Fin h → K) ⧸ relationFiber (attachedExponent ι) (attachedVectors v w) β)

lemma source_capacity_le_core (hh : h=k*(2*s+1).choose s)
    (ι : Fin b ↪ Fin z) (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s),U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (α : Degree (a+z) s) :
    (fiberCapacity ι v w α.val : ℝ)  ≤ 
      (k : ℝ)*(profileAmbientCapacity s-if (corePart α.val).degree=s then 1 else 0) := by
  rw [← source_capacity_real hh v hv α]
  apply Nat.cast_le.mpr
  have hle : relationFiber (coreExponent z) v α.val  ≤ 
      relationFiber (attachedExponent ι) (attachedVectors v w) α.val := by
    rw [relationFiber_attached]
    exact le_sup_left
  exact LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hle)

lemma coarse_capacity_le_regular (hh : h=k*(2*s+1).choose s)
    (ι : Fin b ↪ Fin z) (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s),U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (β : Degree (a+z) (2*s+1)) (hβ : β∉badTargets ι) :
    h-k*(corePart β.val).degree.choose s  ≤  fiberCapacity ι v w β.val := by
  have hp : ∀ i,¬privateExponent a s ι i ≤ β.val := by
    intro i hi
    exact hβ (mem_filter.mpr ⟨mem_univ _,i,hi⟩)
  unfold fiberCapacity
  rw [relationFiber_regular ι v w β.val hp]
  apply (Nat.cast_le (α := ℝ)).mp
  rw [coarse_capacity_real hh β]
  exact target_capacity_real_lower hh v hv β

lemma private_finite_shadow_bound (hh : h=k*(2*s+1).choose s)
    (hs : 0 < s) (hn : 0 < a+z) (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s),U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (ell : Degree (a+z) s → ℕ) (hell : ∀ α,ell α ≤ fiberCapacity ι v w α.val) :
    let p := privateSourceEmbedding (a := a) hs ι
    let reg := ShadowDeletion.regularPart p ell
    let rel := fun (α : Degree (a+z) s) (β : Degree (a+z) (2*s+1)) => α.val ≤ β.val
    (∑ β,ShadowDeletion.shadow rel reg (fun β => h-k*(corePart β.val).degree.choose s) β)+
      (privateGoodMultipliers a s ι).card*(∑ i,ell (p i))  ≤ 
    (∑ β,ShadowDeletion.shadow rel ell (fun β => fiberCapacity ι v w β.val) β)+
      h*(b*(a+z+s-1).choose s)*(∑ α,reg α) := by
  classical
  dsimp only
  let p := privateSourceEmbedding (a := a) hs ι
  let rel := fun (α : Degree (a+z) s) (β : Degree (a+z) (2*s+1)) => α.val ≤ β.val
  have hbound := ShadowDeletion.private_shadow_bookkeeping rel p ell
    (fun β => h-k*(corePart β.val).degree.choose s) (fun β => fiberCapacity ι v w β.val)
    (badTargets ι) (privateGoodTargets ι) (b*(a+z+s-1).choose s) h
    (fun β => Nat.sub_le _ _)
    (by
      intro α hα
      apply card_bad_regular_targets hn ι α
      intro i hi
      apply hα
      exact mem_map.mpr ⟨i,mem_univ _,Subtype.ext hi.symm⟩)
    (coarse_capacity_le_regular hh ι v w hv)
    (privateGoodTargets_disjoint hs ι) (privateGoodTargets_subset_bad ι)
    (by
      intro i β hβ
      have hp := privateGoodTargets_properties hs ι i hβ
      refine ⟨hp.2.1,?_⟩
      have hcap := private_good_capacity hs ι v w i β.val hp.1 hp.2.1 hp.2.2
      change ell (p i) ≤ fiberCapacity ι v w β.val
      rw [show fiberCapacity ι v w β.val=fiberCapacity ι v w (p i).val from hcap]
      exact hell (p i))
  simpa only [privateGoodTargets_card,← mul_sum] using hbound

end Froberg.PrivateColumns
