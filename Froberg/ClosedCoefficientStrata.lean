import Froberg.SlicedCoefficientMotion
import Quartic.ExpansionClosedSlices
import Quartic.AmbientCovectorSpreading

/-! Constructing the closed determinantal slices required by the final
coefficient-motion theorem from explicit Grassmannian incidence budgets. -/
noncomputable section
namespace Froberg.CoefficientMotion
open Module MvPolynomial Quartic
open BilinearCovectorCharts BilinearCoefficientKernel PolynomialBilinearCoordinates
variable {K H : Type*} [Field K] [Infinite K] [IsAlgClosed K]
variable [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable {a b T f : ℕ}
variable (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
variable (E : H →ₗ[K] (Fin f → Fin a → K))

/-- The exact number of slices paid for by coefficient equations and by
auxiliary target columns. -/
def coefficientSliceCount (h f T k : ℕ) : ℕ := (h-f*k)+(T-h)

theorem coefficientSliceCount_antitone (h f T : ℕ) : Antitone (coefficientSliceCount h f T) := by
  intro i j hij
  exact Nat.add_le_add_right (Nat.sub_le_sub_left (Nat.mul_le_mul_left f hij) h) _

/-- Explicit scalar-shadow incidence budgets produce actual motions of
maximal rank; closed-locus existence is proved here, not assumed. -/
theorem exists_maximal_motion_of_incidence_budget (hE : Function.Injective E)
    (hbudget : ∀ ell : Fin T → K, ell ≠ 0 →
      let k := finrank K (LinearMap.ker (relationMap mu ell))
      let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
      (k*(a-k) : ℕ)+(T : ℤ)-e-1 <
        (coefficientSliceCount (finrank K H) f T k : ℕ)) :
    ∃ z : Fin f → Fin b → K,
      finrank K (motion mu E z).range = min (finrank K H) T := by
  classical
  let s := coefficientSliceCount (finrank K H) f T
  obtain ⟨P,⟨x,hx⟩,hgood⟩ := ExpansionClosedSlices.principal_open_all_thresholds (q := 0)
    mu s (coefficientSliceCount_antitone _ _ _) (by
      intro ell hell
      simpa using hbudget ell hell)
  let old : Fin 0 → Fin a → K := fun i => Fin.elim0 i
  let scalars : Fin 0 → Fin b → K := fun i => Fin.elim0 i
  let count : Fin (a+1) → ℕ := fun k =>
    Fintype.card (AmbientCovectorSpreading.Index a b 0 0 k.val)
  let degrees : ∀ k : Fin (a+1), Fin (count k) → ℕ := fun k =>
    AmbientCovectorSpreading.finiteDegree a b 0 0 k.val
  let eqs : ∀ k : Fin (a+1), (j : Fin (count k)) → Forms K T (degrees k j) := fun k =>
    AmbientCovectorSpreading.finiteOriginalEquations (d := k.val) mu old scalars
  let cuts : ∀ k : Fin (a+1), Fin (s k.val) → Forms K T 1 := fun k =>
    AmbientCovectorSpreading.slices (x.2 k)
  apply exists_maximal_motion mu E hE count (fun k => s k.val) degrees eqs cuts
  · intro k ell heqs hcuts
    have he := (AmbientCovectorSpreading.finite_original_equations_iff
      (d := k.val) mu old scalars (by have hk := k.isLt; omega) ell).mp
        (by simpa only [eqs,aeval_eq_eval] using heqs)
    apply hgood x hx k ell (by simpa using he.1)
    constructor
    · intro i
      exact Fin.elim0 i
    · intro j
      simpa only [cuts,AmbientCovectorSpreading.slices,aeval_eq_eval,
        ClosedCovectorEquations.eval_linearForm] using hcuts j
  · intro ell k hk
    apply (AmbientCovectorSpreading.finite_original_equations_iff
      (d := k.val) mu old scalars (by have hj := k.isLt; omega) ell).mpr
    exact ⟨by omega,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  · intro k
    exact le_rfl

/-- A uniform shadow slope larger than the Grassmannian and coefficient
costs supplies the literal integer budget, capped at the whole target. -/
theorem incidence_budget_of_capped_shadow
    (hgrowth : ∀ L : Submodule K (Fin a → K),
      min T ((a+f)*finrank K L) ≤ finrank K (BilinearImage.image mu L)) :
    ∀ ell : Fin T → K, ell ≠ 0 →
      let k := finrank K (LinearMap.ker (relationMap mu ell))
      let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
      (k*(a-k) : ℕ)+(T : ℤ)-e-1 <
        (coefficientSliceCount (finrank K H) f T k : ℕ) := by
  intro ell hell
  let L := LinearMap.ker (relationMap mu ell)
  have he : finrank K (BilinearImage.image mu L) < T :=
    PolynomialSubspaceCovectorCharts.image_finrank_lt mu L ell hell (kernel_image_annihilated mu ell)
  have hg := hgrowth L
  have hmin : (a+f)*finrank K L ≤ finrank K (BilinearImage.image mu L) := by omega
  have hk : finrank K L ≤ a := by simpa using L.finrank_le
  have hprod : finrank K L*(a-finrank K L)+f*finrank K L ≤ finrank K (BilinearImage.image mu L) := by
    calc
      _ ≤ finrank K L*a+f*finrank K L := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
      _ = (a+f)*finrank K L := by ring
      _ ≤ _ := hmin
  have hs : T ≤ coefficientSliceCount (finrank K H) f T (finrank K L)+f*finrank K L := by
    unfold coefficientSliceCount
    omega
  change (finrank K L*(a-finrank K L) : ℕ)+(T : ℤ)-finrank K (BilinearImage.image mu L)-1 <
    (coefficientSliceCount (finrank K H) f T (finrank K L) : ℕ)
  omega

/-- A concrete sufficient scalar-shadow inequality for C.6, with every
incidence and closed-slice step discharged. -/
theorem exists_maximal_motion_of_capped_shadow (hE : Function.Injective E)
    (hgrowth : ∀ L : Submodule K (Fin a → K),
      min T ((a+f)*finrank K L) ≤ finrank K (BilinearImage.image mu L)) :
    ∃ z : Fin f → Fin b → K,
      finrank K (motion mu E z).range = min (finrank K H) T :=
  exists_maximal_motion_of_incidence_budget mu E hE
    (incidence_budget_of_capped_shadow (H := H) mu hgrowth)

end Froberg.CoefficientMotion
