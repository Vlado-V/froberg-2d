import Froberg.ProjectedTopOpen
import Froberg.AugmentedTopBudget

/-! Generic C.9 with exactly the manuscript's scalar augmentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Filter Module TensorProduct MvPolynomial Quartic
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K] {h m e b qF qS : ℕ}

abbrev ProjectedTopParameters (K : Type*) [Field K] (h m e qF qS : ℕ) :=
  (Fin qF → Forms K h 1 ⊗[K] Forms K m e) × (Fin qS → Forms K m (1+e))

def ProjectedTopGeneric (P : Forms K h (1+e) →ₗ[K] (Fin b → K)) (m qF qS : ℕ) : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (ProjectedTopParameters K h m e qF qS))) K,
    (∃ p : ProjectedTopParameters K h m e qF qS,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : ProjectedTopParameters K h m e qF qS,
      eval ((Module.finBasis K _).equivFun p) D≠0 →
      Function.Injective (twoFamilyMultiplication (K := K)
        (V₁ := Forms K h e ⊗[K] Forms K m 1) (V₂ := Fin b → K)
        (projectedTopLinearAction (m := m) P)
        (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e))) p)

theorem eventually_projected_top_generic (hh : 0 < h) (he : 2≤e) (hb : 0 < b)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (hratio : (h : ℝ)/(2*((1+e : ℕ) : ℝ))≤(b : ℝ)/((h+e-1).choose e : ℝ))
    (qF qS : ℕ → ℕ)
    (hF : Tendsto (fun m : ℕ => (qF m : ℝ)/(m : ℝ)^e) atTop
      (𝓝 ((h : ℝ)*criticalRatio (1+e)/(e.factorial : ℝ))))
    (hS : Tendsto (fun m : ℕ => (qS m : ℝ)/(m : ℝ)^(1+e)) atTop
      (𝓝 (criticalRatio (1+e)/((1+e).factorial : ℝ)))) :
    ∀ᶠ m : ℕ in atTop,ProjectedTopGeneric P m (qF m) (qS m+scalarReserveCount (1+e) m) := by
  have hbudget := eventually_augmented_top_budget (show 3≤1+e by omega)
    (Nat.choose_pos (show e≤h+e-1 by omega)) hb hratio qF qS
    (by simpa only [show 1+e-1=e by omega] using hF) hS
  filter_upwards [hbudget,eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  exact projected_top_two_family_open hh hmpos hb P hP hm

end Froberg
