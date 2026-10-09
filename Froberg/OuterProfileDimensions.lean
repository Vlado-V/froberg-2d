module

public import Froberg.OuterCapacityBounds
public import Froberg.MonomialExponentGrowth
public import Froberg.OuterGrowthTransfer

@[expose] public section

/-! Exact source dimensions and target error bounds in the finite profile
normalization used by the transport. -/
noncomputable section
namespace Froberg
open Module Finset MonomialExpansion OuterInjection

lemma attached_quotient_dimension_sum {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    {n s d h : ℕ} (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i, (e i).degree=s) :
    (finrank K ((Fin h → Forms K n (s+d)) ⧸ AttachedMultiplication.relationSpace (d := d) e v he) : ℝ) =
      ∑ β : Degree n (s+d), (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber e v β.val) : ℝ) := by
  have hh := (AttachedMultiplication.quotientFiberEquiv (d := d) e v he).finrank_eq
  rw [Module.finrank_pi_fintype] at hh
  have hr : (finrank K ((Fin h → Forms K n (s+d)) ⧸ AttachedMultiplication.relationSpace (d := d) e v he) : ℝ) =
      ∑ β : Quartic.HomogeneousCoefficientCoordinates.Exponent n (s+d),
        (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber e v β.val) : ℝ) := by exact_mod_cast hh
  rw [hr,← (degreeExponentEquiv n (s+d)).sum_comp]
  rfl

lemma outer_source_dimension_profile {K : Type*} [Field K] {k a z s h : ℕ}
    (hh : h=k*(2*s+1).choose s) (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val)) :
    (finrank K ((Fin h → Forms K (a+z) s) ⧸
      AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)) : ℝ) =
      (k : ℝ)*∑ i, finiteSourceProfile (profileAmbientCapacity s) s a z i := by
  have hd := attached_quotient_dimension_sum (d := 0) (coreExponent z) v (coreExponent_degree z)
  simp only [Nat.add_zero] at hd
  rw [hd]
  simp only [source_capacity_real hh v hv]
  rw [← mul_sum,source_capacity_total]

lemma outer_target_dimension_sum {K : Type*} [Field K] {k a z s h : ℕ}
    (v : Labels k a s → Fin h → K) :
    (finrank K ((Fin h → Forms K (a+z) (s+(s+1))) ⧸
      AttachedMultiplication.relationSpace (d := s+1) (coreExponent z) v (coreExponent_degree z)) : ℝ) =
      ∑ β : Degree (a+z) (2*s+1),
        (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β.val) : ℝ) := by
  have hd := attached_quotient_dimension_sum (d := s+1) (coreExponent z) v (coreExponent_degree z)
  let e : Degree (a+z) (s+(s+1)) ≃ Degree (a+z) (2*s+1) :=
    { toFun := fun β => ⟨β.val, mem_exponents.mpr (by have hβ := degree_val β; omega)⟩
      invFun := fun β => ⟨β.val, mem_exponents.mpr (by have hβ := degree_val β; omega)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact hd.trans (e.sum_comp (fun β =>
    (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β.val) : ℝ)))

lemma outer_target_dimension_budget {K : Type*} [Field K] {k a z s h : ℕ}
    (hh : h=k*(2*s+1).choose s) (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val)) :
    let T := (finrank K ((Fin h → Forms K (a+z) (s+(s+1))) ⧸
      AttachedMultiplication.relationSpace (d := s+1) (coreExponent z) v (coreExponent_degree z)) : ℝ)
    let T₀ := (k : ℝ)*∑ j, finiteTargetProfile s a z j
    T₀ ≤ T ∧ T-T₀ ≤ (h : ℝ)*(a+z)*((a+z+((2*s+1)-2)-1).choose ((2*s+1)-2) : ℝ) := by
  dsimp only
  rw [outer_target_dimension_sum]
  have ht : (∑ β : Degree (a+z) (2*s+1),
      (k : ℝ)*(profileAmbientCapacity s-((corePart β.val).degree.choose s : ℝ))) =
      (k : ℝ)*∑ j, finiteTargetProfile s a z j := by
    rw [← mul_sum]
    congr 1
    exact target_capacity_total a z s
  constructor
  · rw [← ht]
    exact sum_le_sum fun β _ => target_capacity_real_lower hh v hv β
  · have he := target_total_capacity_error (z := z) hh v hv
    rw [ht] at he
    linarith

end Froberg
