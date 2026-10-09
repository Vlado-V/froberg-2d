module

public import Froberg.PrivateLowerGrowth
public import Froberg.PrivateUpperGrowth

@[expose] public section

/-! Combining the two halves of the private-column expansion estimate. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module MonomialExpansion OuterInjection AttachedMultiplication

abbrev CoreIdealGrowth (k a z s : ℕ) (R G : ℝ) : Prop :=
  ∀ (ell : Degree (a+z) s → ℝ) (out : Degree (a+z) (2*s+1) → ℝ),
    (∀ α,0 ≤ ell α ∧ ell α ≤ (k : ℝ)*(profileAmbientCapacity s-if (corePart α.val).degree=s then 1 else 0)) →
    (∀ β,0 ≤ out β) →
    (∀ α β,α.val ≤ β.val →
      min ((k : ℝ)*(profileAmbientCapacity s-((corePart β.val).degree.choose s : ℝ))) (ell α) ≤ out β) →
    R*(∑ α,ell α)+G*min (∑ α,ell α)
      ((k : ℝ)*(∑ i,finiteSourceProfile (profileAmbientCapacity s) s a z i)-∑ α,ell α) ≤ ∑ β,out β

lemma private_uniform_growth_at {K : Type*} [Field K] {a z s k b h : ℕ}
    (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (hn : 0 < a+z) (ι : Fin b ↪ Fin z) (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val))
    (hm : MixedExterior.UniversalMixedPosition u)
    (hA : 0 < finrank K (PrivateSourceSpace ι u))
    (R₀ G₀ Gcore g : ℝ) (hbase : CoreIdealGrowth k a z s R₀ G₀)
    (hcore : ∀ S : Submodule K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))),
      ((finrank K (CoreTargetSpace (z := z) (fun i => u (Sum.inl i))) : ℝ)/
        finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))))*finrank K S+
      Gcore*min (finrank K S : ℝ)
        ((finrank K (CoreSourceSpace (z := z) (fun i => u (Sum.inl i))) : ℝ)-finrank K S) ≤
      (finrank K (outerImage (d := s+1) (coreExponent z) (fun i => u (Sum.inl i)) (coreExponent_degree z) S) : ℝ))
    (hupper : ((b : ℝ)*((a+z+(s+1)-1).choose (s+1) : ℝ))/finrank K (PrivateSourceSpace ι u) ≤ Gcore-g)
    (hregular : (finrank K (PrivateTargetSpace ι u) : ℝ)/finrank K (PrivateSourceSpace ι u)+g+
      (h*((h*2^h)*(a+z+s-1).choose s) : ℕ) ≤ R₀+G₀-(h*(b*(a+z+s-1).choose s) : ℕ))
    (hprivate : (finrank K (PrivateTargetSpace ι u) : ℝ)/finrank K (PrivateSourceSpace ι u)+g+
      (h*((h*2^h)*(a+z+s-1).choose s) : ℕ) ≤ (privateGoodMultipliers a s ι).card) :
    ∀ L : Submodule K (PrivateSourceSpace ι u),
      ((finrank K (PrivateTargetSpace ι u) : ℝ)/finrank K (PrivateSourceSpace ι u))*(finrank K L : ℝ)+
        g*min (finrank K L : ℝ) ((finrank K (PrivateSourceSpace ι u) : ℝ)-finrank K L) ≤
      (finrank K (outerImage (d := s+1) (attachedExponent ι) u (attachedExponent_degree ι) L) : ℝ) := by
  obtain ⟨v,w,rfl⟩ : ∃ (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K),
      attachedVectors v w=u := by
    refine ⟨(fun i => u (Sum.inl i)),(fun i => u (Sum.inr i)),?_⟩
    funext i
    cases i <;> rfl
  intro L
  by_cases hL : 2*finrank K L ≤ finrank K (PrivateSourceSpace ι (attachedVectors v w))
  · have h := private_lower_growth hk hs hh hn ι v w
      hu hm
      R₀ G₀ ((finrank K (PrivateTargetSpace ι (attachedVectors v w)) : ℝ)/finrank K (PrivateSourceSpace ι (attachedVectors v w))+g+
        (h*((h*2^h)*(a+z+s-1).choose s) : ℕ))
      hbase hregular hprivate L hL
    have hLR : 2*(finrank K L : ℝ) ≤ finrank K (PrivateSourceSpace ι (attachedVectors v w)) := by exact_mod_cast hL
    rw [min_eq_left (by linarith)]
    simpa only [add_sub_cancel_right,add_mul] using h
  · have hLR : (finrank K (PrivateSourceSpace ι (attachedVectors v w)) : ℝ)/2 ≤ finrank K L := by
      have hi : finrank K (PrivateSourceSpace ι (attachedVectors v w)) ≤ 2*finrank K L := by omega
      have hiR : (finrank K (PrivateSourceSpace ι (attachedVectors v w)) : ℝ) ≤ 2*(finrank K L : ℝ) := by exact_mod_cast hi
      linarith
    have hb := private_upper_growth hk hs hh hn ι (attachedVectors v w) hu hA Gcore hcore L hLR
    have hcod : 0 ≤ (finrank K (PrivateSourceSpace ι (attachedVectors v w)) : ℝ)-finrank K L := by
      exact sub_nonneg.mpr (by exact_mod_cast Submodule.finrank_le L)
    rw [min_eq_right (by linarith)]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith :
      g ≤ Gcore-((b : ℝ)*((a+z+(s+1)-1).choose (s+1) : ℝ))/finrank K (PrivateSourceSpace ι (attachedVectors v w))) hcod)).trans hb

end Froberg.PrivateColumns
