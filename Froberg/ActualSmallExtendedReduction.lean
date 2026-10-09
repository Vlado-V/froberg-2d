module

public import Froberg.SmallExtendedEvenReduction
public import Froberg.PreparedActualSmallReduction
public import Froberg.ShiftedPreparedCapacities
public import Froberg.ShiftedSmallCapacities
public import Froberg.LateQuadraticCapacity

@[expose] public section

/-! The actual cubic and quartic counts, including a fixed private-variable
reserve and appended columns, satisfy the full common-open construction. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_cubic_extended_reduction_open :
    ∀ᶠ h : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 3*(h : ℝ)^2*(n : ℝ)^(3-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 3 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 3 h →
        let A := Space (v+v+z) 3 (upperCount (v+v+z) 3) (allEvenIndices 3)
          (allEvenCount 3 h (v+v+z) (e (v+v+z)+extra))
          (fun j => Forms K h j⊓(T j).ker)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_quadratic_capacity_shift_late (K := K) (d := 3) (by omega),
    eventually_strong_cubic_diagonal_capacity_shift] with h hquad hstrong
  intro z extra e he
  let q := fun n => upperCount (n+z) 3
  let counts := fun n => allEvenCount 3 h (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices 3) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^3) atTop
      (𝓝 (criticalRatio 3/((3 : ℕ).factorial : ℝ))) :=
    allEvenLabel_count_limit_shift (by omega) h extra z e he
  have hc : ∀ᶠ n : ℕ in atTop, counts n 2≤
      ⌈countBeta 3*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(3-2)⌉₊+extra := by
    filter_upwards [(tendsto_add_atTop_nat z).eventually he] with n hn
    have hb : e (n+z)≤⌈countBeta 3*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(3-2)⌉₊ := by
      exact_mod_cast hn.le.trans (Nat.le_ceil _)
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := 3) (by omega)),
      targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
  have hq := tendsto_twice_nat.eventually
    (hquad (allEvenIndices 3) q counts hcount z extra)
  have hp : ∀ᶠ v : ℕ in atTop,counts (v+v) 2≤
      (2*(h/2).choose 2-deletedTargetCount 3 h)*((v+v)/2) := by
    filter_upwards [tendsto_twice_nat.eventually (hstrong z extra),
      tendsto_twice_nat.eventually hc] with v hv hcv
    have hb := hcv.trans (by simpa only [show 3-2=1 by omega,pow_one] using hv)
    simpa only [two_mul] using hb
  filter_upwards [hq,hp,tendsto_twice_nat.eventually hc,eventually_gt_atTop 0] with v hqv hpv hcv hvpos
  intro X _ _ _ T hX hO
  let O := fun j => Forms K h j⊓(T j).ker
  have hqv' : QuadraticRowCapacity (v+v) 3 (q (v+v))
      (fullSparseBlockCount (countBeta 3) 2 (3-2) h) (allEvenIndices 3) (counts (v+v)) O := by
    simpa only [two_mul] using hqv (Fin h) O hO hcv
  have hpv' : counts (v+v) 2≤
      (2*(h/2).choose 2-finrank K X)*((v+v)/2) := by
    simpa only [hX] using hpv
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  let I := Label (q (v+v)) (allEvenIndices 3) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact finite_cubic_extended_reduction_open T ell hell
    (fun j _ hj => allEvenCount_off_two_small (Or.inl rfl) _ _ _ hj) hpv' ⟨_,hqv'⟩

theorem eventually_actual_quartic_extended_reduction_open :
    ∀ᶠ h : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 4*(h : ℝ)^2*(n : ℝ)^(4-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 4 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 4 h →
        let A := Space (v+v+z) 4 (upperCount (v+v+z) 4) (allEvenIndices 4)
          (allEvenCount 4 h (v+v+z) (e (v+v+z)+extra))
          (fun j => Forms K h j⊓(T j).ker)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_quadratic_capacity_shift_late (K := K) (d := 4) (by omega),
    eventually_strong_quartic_diagonal_capacity_shift] with h hquad hstrong
  intro z extra e he
  let q := fun n => upperCount (n+z) 4
  let counts := fun n => allEvenCount 4 h (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices 4) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^4) atTop
      (𝓝 (criticalRatio 4/((4 : ℕ).factorial : ℝ))) :=
    allEvenLabel_count_limit_shift (by omega) h extra z e he
  have hc : ∀ᶠ n : ℕ in atTop, counts n 2≤
      ⌈countBeta 4*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(4-2)⌉₊+extra := by
    filter_upwards [(tendsto_add_atTop_nat z).eventually he] with n hn
    have hb : e (n+z)≤⌈countBeta 4*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(4-2)⌉₊ := by
      exact_mod_cast hn.le.trans (Nat.le_ceil _)
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := 4) (by omega)),
      targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
  have hq := tendsto_twice_nat.eventually
    (hquad (allEvenIndices 4) q counts hcount z extra)
  have hp : ∀ᶠ v : ℕ in atTop,counts (v+v) 2≤
      (2*(h/2).choose 2-deletedTargetCount 4 h)*((balancedScalarHalf v).card.choose 2/2) := by
    filter_upwards [tendsto_twice_nat.eventually (hstrong z extra),
      tendsto_twice_nat.eventually hc] with v hv hcv
    have hb := hcv.trans (by simpa only [show 4-2=2 by omega] using hv)
    simpa only [two_mul,balancedScalarHalf_card,show (v+v)/2=v by omega] using hb
  obtain ⟨n₀,hn₀⟩ := eventually_small_single_profile_scalar_open (K := K)
    (d := 4) (R := 4) (by omega) (by omega) (Or.inl rfl) le_rfl r hcount
  filter_upwards [hq,hp,tendsto_twice_nat.eventually hc,eventually_ge_atTop n₀,eventually_gt_atTop 0] with v hqv hpv hcv hv hvpos
  intro X _ _ _ T hX hO
  let O := fun j => Forms K h j⊓(T j).ker
  have hqv' : QuadraticRowCapacity (v+v) 4 (q (v+v))
      (fullSparseBlockCount (countBeta 4) 2 (4-2) h) (allEvenIndices 4) (counts (v+v)) O := by
    simpa only [two_mul] using hqv (Fin h) O hO hcv
  have hpv' : counts (v+v) 2≤
      (2*(h/2).choose 2-finrank K X)*((balancedScalarHalf v).card.choose 2/2) := by
    simpa only [hX] using hpv
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  let I := Label (q (v+v)) (allEvenIndices 4) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hbal : (balancedScalarHalf v).card≤(balancedScalarHalf v)ᶜ.card := by
    simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card,le_refl]
  obtain ⟨D,⟨Q,hQ⟩,hgood⟩ := hn₀ (v+v) (by omega) (balancedScalarHalf v) hbal
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega) 2
  exact finite_quartic_extended_reduction_open T ell hell
    (fun j _ hj => allEvenCount_off_two_small (Or.inr rfl) _ _ _ hj)
    (balancedScalarHalf v) hbal hpv' ⟨_,hqv'⟩ Q (by simpa only [show 4-4=0 by omega] using hgood Q hQ)

end Froberg.PreparedParameters
