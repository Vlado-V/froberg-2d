import Froberg.TensorizedGrowth
import Froberg.GradedNormalized

/-! The ordinary normalized multiplication bound for two actual polynomial
variable blocks, including degree-zero factors. -/
noncomputable section
namespace Froberg
open Module TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] {h n a b c e : ℕ}

/-- Tensoring the two uniform divisibility couplings gives the exact ratio of
target dimension to coefficient dimension. -/
theorem biform_normalized_growth (hh : 0<h) (hn : 0<n)
    (L : Submodule K (Forms K h b ⊗[K] Forms K n e)) :
    (h+(b+a)-1).choose (b+a) * (n+e+c-1).choose (e+c) * finrank K L ≤
      (h+b-1).choose b * (n+e-1).choose e *
        finrank K (Quartic.BilinearImage.image
          (tensorFormProduct (d := c) (gradedMultiplication (K := K) (n := h) (d := a) (e := b))) L) := by
  apply tensorized_bilinear_growth _ hn _ _ (fun S => ?_) L
  simpa only [finrank_forms K h (a+b) hh,finrank_forms K h b hh,Nat.add_comm a b] using
    graded_normalized_growth (d := a) hh S

end Froberg
