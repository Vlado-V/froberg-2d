import Froberg.PrivateFiniteShadow
import Froberg.OuterProfileDimensions

/-! The lower-half private-column shadow bound, expressed entirely in the
actual source and target fiber dimensions. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module MonomialExpansion OuterInjection
variable {K : Type*} [Field K] {a z s k b h : ℕ}

lemma private_lower_numeric (hh : h=k*(2*s+1).choose s)
    (hs : 0 < s) (hn : 0 < a+z) (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s),U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (R G P : ℝ)
    (hbase : ∀ (ell : Degree (a+z) s → ℝ) (out : Degree (a+z) (2*s+1) → ℝ),
      (∀ α,0 ≤ ell α ∧ ell α ≤ (k : ℝ)*(profileAmbientCapacity s-if (corePart α.val).degree=s then 1 else 0)) →
      (∀ β,0 ≤ out β) →
      (∀ α β,α.val ≤ β.val →
        min ((k : ℝ)*(profileAmbientCapacity s-((corePart β.val).degree.choose s : ℝ))) (ell α) ≤ out β) →
      R*(∑ α,ell α)+G*min (∑ α,ell α)
        ((k : ℝ)*(∑ i,finiteSourceProfile (profileAmbientCapacity s) s a z i)-∑ α,ell α) ≤ ∑ β,out β)
    (hregular : P ≤ R+G-(h*(b*(a+z+s-1).choose s) : ℕ))
    (hprivate : P ≤ (privateGoodMultipliers a s ι).card)
    (ell : Degree (a+z) s → ℕ) (hell : ∀ α,ell α ≤ fiberCapacity ι v w α.val)
    (hlow : 2*(∑ α,ell α : ℕ) ≤
      (k : ℝ)*(∑ i,finiteSourceProfile (profileAmbientCapacity s) s a z i)) :
    P*(∑ α,ell α : ℕ) ≤
      (∑ β,ShadowDeletion.shadow (fun α β => α.val ≤ β.val) ell
        (fun β : Degree (a+z) (2*s+1) => fiberCapacity ι v w β.val) β : ℕ) := by
  classical
  let p := privateSourceEmbedding (a := a) hs ι
  let reg := ShadowDeletion.regularPart p ell
  let rel := fun (α : Degree (a+z) s) (β : Degree (a+z) (2*s+1)) => α.val ≤ β.val
  let old := ShadowDeletion.shadow rel reg (fun β => h-k*(corePart β.val).degree.choose s)
  have hreg (α : Degree (a+z) s) : reg α ≤ ell α := ShadowDeletion.regularPart_le p ell α
  have hsum : (∑ α,reg α) ≤ ∑ α,ell α := sum_le_sum (fun α _ => hreg α)
  have hb := hbase (fun α => (reg α : ℝ)) (fun β => (old β : ℝ))
    (by
      intro α
      refine ⟨Nat.cast_nonneg _,?_⟩
      exact (Nat.cast_le.mpr ((hreg α).trans (hell α))).trans (source_capacity_le_core hh ι v w hv α))
    (fun _ => Nat.cast_nonneg _)
    (by
      intro α β hab
      rw [← coarse_capacity_real hh β,min_comm]
      exact_mod_cast ShadowDeletion.min_le_shadow rel reg
        (fun β => h-k*(corePart β.val).degree.choose s) α β hab)
  have hsumR : (∑ α,reg α : ℕ) ≤ (∑ α,ell α : ℕ) := hsum
  have hsumR' : ((∑ α,reg α : ℕ) : ℝ) ≤ (∑ α,ell α : ℕ) := by exact_mod_cast hsumR
  have hm : min ((∑ α,reg α : ℕ) : ℝ)
      ((k : ℝ)*(∑ i,finiteSourceProfile (profileAmbientCapacity s) s a z i)-(∑ α,reg α : ℕ)) =
      (∑ α,reg α : ℕ) := min_eq_left (by linarith)
  rw [← Nat.cast_sum,← Nat.cast_sum,hm] at hb
  have hfinite := private_finite_shadow_bound hh hs hn ι v w hv ell hell
  have hfR := (Nat.cast_le (α := ℝ)).mpr hfinite
  have hsplit := ShadowDeletion.sum_regularPart p ell
  have hsplitR : ((∑ α,reg α : ℕ) : ℝ)+(∑ i,ell (p i) : ℕ)=(∑ α,ell α : ℕ) := by exact_mod_cast hsplit
  have hregprod := mul_le_mul_of_nonneg_right hregular (Nat.cast_nonneg (∑ α,reg α))
  have hprivprod := mul_le_mul_of_nonneg_right hprivate (Nat.cast_nonneg (∑ i,ell (p i)))
  push_cast at hfR
  change P*(∑ α,ell α : ℕ) ≤ _
  dsimp only [p,reg,rel,old] at *
  push_cast at hb hsplitR hregprod hprivprod ⊢
  nlinarith

end Froberg.PrivateColumns
