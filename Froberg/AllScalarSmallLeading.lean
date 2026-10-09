module

public import Froberg.ExtendedLeadingWitnesses
public import Froberg.LateQuadraticCapacity
public import Froberg.PreparedActualSmallReduction
public import Froberg.NaturalEventualParity

@[expose] public section

/-! All leading-row witnesses for degrees three and four, uniformly in
late output constraints and in the parity of the scalar dimension. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_small_leading_shift {d : ℕ} (hd : d=3 ∨ d=4) :
    ∀ᶠ h : ℕ in atTop,∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      let A := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
        (allEvenCount d h (v+v+z) (e (v+v+z)+extra))
        (fun j => Forms K h j⊓(T j).ker)
      ∀ R : allEvenIndices d,∃ p : A,LinearIndependent K (p.2 R) := by
  classical
  have hd3 : 3≤d := by omega
  filter_upwards [eventually_quadratic_capacity_shift_late (K := K) hd3] with h hquad
  intro z extra e he
  let q := fun n => upperCount (n+z) d
  let counts := fun n => allEvenCount d h (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices d) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    allEvenLabel_count_limit_shift hd3 h extra z e he
  have hc : ∀ᶠ n : ℕ in atTop, counts n 2≤
      ⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊+extra := by
    filter_upwards [(tendsto_add_atTop_nat z).eventually he] with n hn
    have hb : e (n+z)≤⌈countBeta d*(h : ℝ)^2*((n+z : ℕ) : ℝ)^(d-2)⌉₊ := by
      exact_mod_cast hn.le.trans (Nat.le_ceil _)
    simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices hd3),
      targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
  have hq := tendsto_twice_nat.eventually (hquad (allEvenIndices d) q counts hcount z extra)
  filter_upwards [hq,tendsto_twice_nat.eventually hc,eventually_gt_atTop 0] with v hqv hcv hv
  intro X _ _ _ T hO
  let O := fun j => Forms K h j⊓(T j).ker
  have hcap : QuadraticRowCapacity (v+v) d (q (v+v))
      (fullSparseBlockCount (countBeta d) 2 (d-2) h) (allEvenIndices d) (counts (v+v)) O := by
    simpa only [two_mul] using hqv (Fin h) O hO hcv
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  exact quadratic_only_extended_leading hd3 (fun _ _ => inf_le_left)
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩)
    (fun j _ hj => allEvenCount_off_two_small hd _ _ _ hj) ⟨_,hcap⟩ ell hell

theorem eventually_actual_small_leading_all_scalars {d : ℕ} (hd : d=3 ∨ d=4) :
    ∀ᶠ h : ℕ in atTop,∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension d h →
      let A := Space n d (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∀ R : allEvenIndices d,∃ p : A,LinearIndependent K (p.2 R) := by
  filter_upwards [eventually_actual_small_leading_shift (K := K) hd] with h hh
  intro extra e he
  exact eventually_of_twice_add_shifts 0 _ (hh 0 extra e he) (hh 1 extra e he)

theorem eventually_actual_cubic_leading_witnesses_all_scalars :
    ∀ᶠ h : ℕ in atTop,∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 3*(h : ℝ)^2*(n : ℝ)^(3-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 3 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 3 h →
      let A := Space n 3 (upperCount n 3) (allEvenIndices 3)
        (allEvenCount 3 h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∀ R : allEvenIndices 3,∃ p : A,LinearIndependent K (p.2 R) := by
  filter_upwards [eventually_actual_small_leading_all_scalars (K := K) (d := 3) (Or.inl rfl)] with h hh
  intro extra e he
  filter_upwards [hh extra e he] with n hn
  intro X _ _ _ T _ hO
  exact hn X T hO

theorem eventually_actual_quartic_leading_witnesses_all_scalars :
    ∀ᶠ h : ℕ in atTop,∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta 4*(h : ℝ)^2*(n : ℝ)^(4-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → Poly K h →ₗ[K] X,
      finrank K X=deletedTargetCount 4 h →
      finrank K ↥(Forms K h 2⊓(T 2).ker)=quadraticOutputDimension 4 h →
      let A := Space n 4 (upperCount n 4) (allEvenIndices 4)
        (allEvenCount 4 h n (e n+extra)) (fun j => Forms K h j⊓(T j).ker)
      ∀ R : allEvenIndices 4,∃ p : A,LinearIndependent K (p.2 R) := by
  filter_upwards [eventually_actual_small_leading_all_scalars (K := K) (d := 4) (Or.inr rfl)] with h hh
  intro extra e he
  filter_upwards [hh extra e he] with n hn
  intro X _ _ _ T _ hO
  exact hn X T hO

end Froberg.PreparedParameters
