module

public import Froberg.ThinShadowBudget
public import Froberg.ClosedCoefficientStrata

@[expose] public section

/-! The exact natural-number slice budget that turns the C.4 thin-stratum
estimate into the C.6 maximal-normal-rank criterion. -/
noncomputable section
namespace Froberg
open BilinearCovectorStrata CoefficientMotion

theorem thinSlices_le_coefficientSliceCount (h f T k : ℕ) (C : ℝ)
    (hf : (f : ℝ) ≤ C) :
    thinSlices T C k ≤ coefficientSliceCount h f T k := by
  have hprod : ((f*k : ℕ) : ℝ) ≤ C*k := by
    push_cast
    exact mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg k)
  have hceil : f*k ≤ Nat.ceil (C*k) := by
    exact_mod_cast hprod.trans (Nat.le_ceil (C*k))
  unfold thinSlices coefficientSliceCount
  omega

end Froberg
