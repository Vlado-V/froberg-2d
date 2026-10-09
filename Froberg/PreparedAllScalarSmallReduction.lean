module

public import Froberg.PreparedSmallExtendedReduction
public import Froberg.PreparedLateMiddleSmallReduction
public import Froberg.PrivateBiformFamily
public import Froberg.NaturalEventualParity

@[expose] public section

/-! Exact small-degree counts yield the prepared reduction for every
sufficiently large scalar dimension, with output data chosen afterwards. -/
noncomputable section
set_option maxHeartbeats 2600000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_middle_extended_reduction_open_late_output {d : ℕ}
    (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) → T 4=0 →
      let A := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
        (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
      ∃ D : MvPolynomial (Fin (finrank K A)) K,
        (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
        ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_actual_middle_small_witnesses_shift_late_output (K := K) hd hd8,
    eventually_counted_fourth_row_capacity_shift_late_output (K := K) hd hd8,
    tendsto_twice_nat.eventually (eventually_quadratic_capacity_shift_late (K := K) (d := d) (by omega))]
    with w hcore hfour hquad
  intro hdiv z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*((2*w : ℕ) : ℝ)^2*(n : ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q := fun n => upperCount (n+z) d
  let counts := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  have hcount := allEvenLabel_count_limit_shift (by omega : 3≤d) (2*w) extra z e hecast
  filter_upwards [hcore hdiv z extra e he,hfour z extra e he,
    tendsto_twice_nat.eventually (hquad (allEvenIndices d) q counts hcount z extra),
    tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast),
    eventually_gt_atTop (0 : ℕ)] with v hc hf hq hev hv
  intro X _ _ _ T hX hO hT
  have hb : e (2*v+z)≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊ := by
    exact_mod_cast hev.le.trans (Nat.le_ceil _)
  have hcb : counts (2*v) 2≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊+extra := by
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := d) (by omega)),
      targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
  have hqv : QuadraticRowCapacity (v+v) d (q (v+v))
      (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
      (counts (v+v)) (constrainedOutputs T) := by
    simpa only [two_mul] using hq (Fin w × Bool) (constrainedOutputs T) hO hcb
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  let I := Label (q (v+v)) (allEvenIndices d) (counts (v+v))
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hc' := hc X T hX hO hT
  exact small_extended_reduction_open hd T
    (fun j _ hj2 hj4 => allEvenCount_off_two_four_small hd8 _ _ _ hj2 hj4)
    ⟨_,hqv⟩ ⟨_,hf X T hX hT⟩ hc'.1 hc'.2 ell hell

theorem eventually_actual_middle_all_scalar_reduction_open_late_output {d : ℕ}
    (hd : 5≤d) (hd8 : d≤8) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ m : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) → T 4=0 →
      let A := Space m d (upperCount m d) (allEvenIndices d)
        (allEvenCount d (2*w) m (e m+extra)) (constrainedOutputs T)
      ∃ D : MvPolynomial (Fin (finrank K A)) K,
        (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
        ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  filter_upwards [eventually_actual_middle_extended_reduction_open_late_output (K := K) hd hd8] with w hw
  intro hdiv extra e he
  exact eventually_of_twice_add_shifts 0 _ (hw hdiv 0 extra e he) (hw hdiv 1 extra e he)

end Froberg.PreparedParameters
