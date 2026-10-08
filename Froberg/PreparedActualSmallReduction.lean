import Froberg.PreparedSmallEvenReduction
import Froberg.ShiftedPreparedCapacities
import Froberg.ShiftedSmallCapacities

/-! The actual cubic and quartic counts, including a fixed private-variable
reserve and appended columns, satisfy the full common-open construction. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem allEvenCount_off_two_small {d : ℕ} (hd : d=3 ∨ d=4)
    (h n e : ℕ) {j : ℕ} (hj : j≠2) : allEvenCount d h n e j=0 := by
  apply allEvenCount_inactive
  intro ha
  have hb := activeEvenIndices_bounds (by omega : 3≤d) ha
  have he := Nat.even_iff.mp hb.2.2
  omega

theorem eventually_actual_cubic_reduction_open_shift :
    ∀ᶠ h : ℕ in atTop,
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 3 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 3 h →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 3*(h : ℝ)^2*(n : ℝ)^(3-2)) →
      ∀ᶠ v : ℕ in atTop,
        let A := Space (v+v) 3 (upperCount (v+v+z) 3) (allEvenIndices 3)
          (allEvenCount 3 h (v+v+z) (e (v+v+z)+extra))
          (fun j => Forms K h j⊓(T j).ker)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_quadratic_capacity_shift (K := K) (d := 3) (by omega),
    eventually_strong_cubic_diagonal_capacity_shift] with h hquad hstrong
  intro T hX hO z extra e he
  let O := fun j => Forms K h j⊓(T j).ker
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
  have hq : ∀ᶠ v : ℕ in atTop,QuadraticRowCapacity (v+v) 3 (q (v+v))
      (fullSparseBlockCount (countBeta 3) 2 (3-2) h) (allEvenIndices 3) (counts (v+v)) O := by
    filter_upwards [tendsto_twice_nat.eventually
      (hquad (Fin h) O hO (allEvenIndices 3) q counts hcount z extra),
      tendsto_twice_nat.eventually hc] with v hv hcv
    simpa only [two_mul] using hv hcv
  have hp : ∀ᶠ v : ℕ in atTop,counts (v+v) 2≤
      (2*(h/2).choose 2-finrank K X)*((v+v)/2) := by
    filter_upwards [tendsto_twice_nat.eventually (hstrong z extra),
      tendsto_twice_nat.eventually hc] with v hv hcv
    have hb := hcv.trans (by simpa only [show 3-2=1 by omega,pow_one] using hv)
    simpa only [two_mul,hX] using hb
  filter_upwards [hq,hp] with v hqv hpv
  let I := Label (q (v+v)) (allEvenIndices 3) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact finite_cubic_reduction_open T
    (fun j _ hj => allEvenCount_off_two_small (Or.inl rfl) _ _ _ hj) hpv ⟨_,hqv⟩

theorem eventually_actual_quartic_reduction_open_shift :
    ∀ᶠ h : ℕ in atTop,
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 4 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 4 h →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 4*(h : ℝ)^2*(n : ℝ)^(4-2)) →
      ∀ᶠ v : ℕ in atTop,
        let A := Space (v+v) 4 (upperCount (v+v+z) 4) (allEvenIndices 4)
          (allEvenCount 4 h (v+v+z) (e (v+v+z)+extra))
          (fun j => Forms K h j⊓(T j).ker)
        ∃ D : MvPolynomial (Fin (finrank K A)) K,
          (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
          ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_quadratic_capacity_shift (K := K) (d := 4) (by omega),
    eventually_strong_quartic_diagonal_capacity_shift] with h hquad hstrong
  intro T hX hO z extra e he
  let O := fun j => Forms K h j⊓(T j).ker
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
  have hq : ∀ᶠ v : ℕ in atTop,QuadraticRowCapacity (v+v) 4 (q (v+v))
      (fullSparseBlockCount (countBeta 4) 2 (4-2) h) (allEvenIndices 4) (counts (v+v)) O := by
    filter_upwards [tendsto_twice_nat.eventually
      (hquad (Fin h) O hO (allEvenIndices 4) q counts hcount z extra),
      tendsto_twice_nat.eventually hc] with v hv hcv
    simpa only [two_mul] using hv hcv
  have hp : ∀ᶠ v : ℕ in atTop,counts (v+v) 2≤
      (2*(h/2).choose 2-finrank K X)*((balancedScalarHalf v).card.choose 2/2) := by
    filter_upwards [tendsto_twice_nat.eventually (hstrong z extra),
      tendsto_twice_nat.eventually hc] with v hv hcv
    have hb := hcv.trans (by simpa only [show 4-2=2 by omega] using hv)
    simpa only [two_mul,hX,balancedScalarHalf_card,show (v+v)/2=v by omega] using hb
  obtain ⟨n₀,hn₀⟩ := eventually_small_single_profile_scalar_open (K := K)
    (d := 4) (R := 4) (by omega) (by omega) (Or.inl rfl) le_rfl r hcount
  filter_upwards [hq,hp,eventually_ge_atTop n₀] with v hqv hpv hv
  let I := Label (q (v+v)) (allEvenIndices 4) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hbal : (balancedScalarHalf v).card≤(balancedScalarHalf v)ᶜ.card := by
    simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card,le_refl]
  obtain ⟨D,⟨Q,hQ⟩,hgood⟩ := hn₀ (v+v) (by omega) (balancedScalarHalf v) hbal
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega) 2
  exact finite_quartic_reduction_open T
    (fun j _ hj => allEvenCount_off_two_small (Or.inr rfl) _ _ _ hj)
    (balancedScalarHalf v) hbal hpv ⟨_,hqv⟩ Q (by simpa only [show 4-4=0 by omega] using hgood Q hQ)

end Froberg.PreparedParameters
