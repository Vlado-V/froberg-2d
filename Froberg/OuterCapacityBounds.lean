import Froberg.SourceFibers
import Froberg.CoreDivisorCount
import Froberg.ProfileCapacityDrop

/-! Exact real-valued source capacities and coarse target capacities for
one and the same actual attached presentation. -/
noncomputable section
namespace Froberg.OuterInjection
open Module Finset MonomialExpansion
variable {K : Type*} [Field K]

lemma core_fiber_labels_independent {k a z s h : ℕ}
    (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (β : Fin (a+z) →₀ ℕ) (hb : k*β.degree.choose s ≤ h) :
    LinearIndependent K (fun i : {i : Labels k a s // coreExponent z i ≤ β} => v i.val) := by
  classical
  let U := univ.filter (fun i : Labels k a s => coreExponent z i ≤ β)
  have hU : U.card ≤ h := by
    have hc := (card_target_labels_le (k := k) (s := s) z β).trans hb
    simpa only [Fintype.card_subtype] using hc
  let f : {i : Labels k a s // coreExponent z i ≤ β} → U := fun i =>
    ⟨i.val, mem_filter.mpr ⟨mem_univ _,i.property⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg (fun t : U => t.val) hij)
  exact (hv U hU).comp f hf

lemma outer_multiplicity_le {k s h : ℕ} (hh : h=k*(2*s+1).choose s) : k ≤ h := by
  rw [hh]
  have hH := Nat.choose_pos (show s ≤ 2*s+1 by omega)
  nlinarith

lemma source_capacity_real {k a z s h : ℕ}
    (hh : h=k*(2*s+1).choose s) (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (α : Degree (a+z) s) :
    (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v α.val) : ℝ) =
      (k : ℝ)*(profileAmbientCapacity s - if (corePart α.val).degree=s then 1 else 0) := by
  have hk := outer_multiplicity_le hh
  have hhR : (h : ℝ) = (k : ℝ)*profileAmbientCapacity s := by exact_mod_cast hh
  rw [source_quotientFiber_finrank_of_general_position hk v hv α.val (degree_val α)]
  split_ifs
  · rw [Nat.cast_sub hk,hhR]
    ring
  · rw [hhR]
    ring

lemma coarse_capacity_real {k a z s h : ℕ} (hh : h=k*(2*s+1).choose s)
    (β : Degree (a+z) (2*s+1)) :
    ((h-k*(corePart β.val).degree.choose s : ℕ) : ℝ) =
      (k : ℝ)*(profileAmbientCapacity s - ((corePart β.val).degree.choose s : ℝ)) := by
  have hc : (corePart β.val).degree ≤ 2*s+1 := by
    simpa only [degree_val] using corePart_le_degree β.val
  have hm : k*(corePart β.val).degree.choose s ≤ h := by
    rw [hh]
    exact Nat.mul_le_mul_left k (Nat.choose_le_choose s hc)
  rw [Nat.cast_sub hm,Nat.cast_mul]
  have hhR : (h : ℝ) = (k : ℝ)*profileAmbientCapacity s := by exact_mod_cast hh
  rw [hhR]
  ring

lemma target_capacity_real_lower {k a z s h : ℕ} (hh : h=k*(2*s+1).choose s)
    (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (β : Degree (a+z) (2*s+1)) :
    (k : ℝ)*(profileAmbientCapacity s - ((corePart β.val).degree.choose s : ℝ)) ≤
      (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β.val) : ℝ) := by
  rw [← coarse_capacity_real hh β]
  apply Nat.cast_le.mpr
  apply AttachedMultiplication.core_quotientFiber_capacity
  apply core_fiber_labels_independent v hv
  rw [degree_val,← hh]

lemma target_total_capacity_error {k a z s h : ℕ} (hh : h=k*(2*s+1).choose s)
    (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val)) :
    (∑ β : Degree (a+z) (2*s+1),
      (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β.val) : ℝ)) ≤
    (∑ β : Degree (a+z) (2*s+1),
      (k : ℝ)*(profileAmbientCapacity s - ((corePart β.val).degree.choose s : ℝ))) +
    (h : ℝ)*(a+z)*((a+z+((2*s+1)-2)-1).choose ((2*s+1)-2) : ℝ) := by
  have hi (β : Degree (a+z) (2*s+1)) := core_fiber_labels_independent v hv β.val
    (by rw [degree_val,← hh])
  have ht := AttachedMultiplication.coarse_target_error v hi
  have htR : (∑ β : Degree (a+z) (2*s+1),
      (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β.val) : ℝ)) ≤
    (∑ β : Degree (a+z) (2*s+1), ((h-k*(corePart β.val).degree.choose s : ℕ) : ℝ)) +
    (h : ℝ)*(a+z)*((a+z+((2*s+1)-2)-1).choose ((2*s+1)-2) : ℝ) := by exact_mod_cast ht
  simpa only [coarse_capacity_real hh] using htR

end Froberg.OuterInjection
