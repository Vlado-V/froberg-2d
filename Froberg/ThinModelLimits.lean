module

public import Froberg.ThinQuotientStrata
public import Froberg.ThinShadowLimits

@[expose] public section

/-! Uniform thin-case covector strata from the strict vector-model estimates. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Filter Module MvPolynomial Quartic PolynomialBilinearCoordinates VectorMultiplicationCoordinates
open BilinearScalarFamily
open scoped Topology
variable {K : Type*} [Field K] [Infinite K] {h s : ℕ}

theorem eventually_generic_thin_model_strata
    (c q j : ℕ → ℕ) (g : (n : ℕ) → Fin (c n) → Rows K h n s)
    (G α : ℝ) (hG : 0 < G) (hα : 0 < α)
    (hg : ∀ᶠ n in atTop,StrictModel (g n) (s+1) (G*(n : ℝ)^(s+1)))
    (hA : Tendsto (fun n : ℕ => (finrank K (Source (g n)) : ℝ)/(n : ℝ)^s) atTop (𝓝 α))
    (hJ : Tendsto (fun n : ℕ => (j n : ℝ)/(n : ℝ)^(2*s+1)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop,finrank K (Target (g n) (s+1))=q n*finrank K (Source (g n))+j n) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n in atTop,
      ∃ P : MvPolynomial (Fin (q n) × Fin (finrank K (Forms K n (s+1)))) K,
        (∃ Q : Fin (q n) → Forms K n (s+1),
          eval (fun ik => coordinates K _ (Q ik.1) ik.2) P ≠ 0) ∧
        ∀ Q : Fin (q n) → Forms K n (s+1),
          eval (fun ik => coordinates K _ (Q ik.1) ik.2) P ≠ 0 →
          Function.Injective (BilinearScalarFamily.multiplication (quotientMultiplication (g n) (s+1)) Q) ∧
          finrank K (ScalarQuotient (quotientMultiplication (g n) (s+1)) Q)=j n ∧
          HasClosedKernelSlices (scalarQuotientBilinear (quotientMultiplication (g n) (s+1)) Q)
            (BilinearCovectorStrata.thinSlices (j n) (C*(n : ℝ)^(s+1))) := by
  have hb := thin_shadow_eventual_budget (fun n => (finrank K (Source (g n)) : ℝ))
    (fun n => (j n : ℝ)) s α G hα hG hA hJ
  refine ⟨G/2,by positivity,?_⟩
  filter_upwards [hg,hT,hb] with n hgn hTn hbn
  exact hgn.generic_thin_quotient_strata hTn (by positivity) hbn.1 hbn.2

end Froberg.VectorExpansionOpen
