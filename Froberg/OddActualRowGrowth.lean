module

public import Froberg.OddBackgroundRowProjection
public import Froberg.BilinearParameterTransport
public import Froberg.ScalarBiformParameter

@[expose] public section

/-! Uniform middle-row scalar growth uses the actual scalar polynomial
space, with its harmless degree-zero output factor removed. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d b q f : ℕ}

def oddActualRowScalarAction (hb : 1 ≤ b) (hbd : b ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Forms K m d →ₗ[K] (Forms K h b ⊗[K] Forms K m (d-b)) →ₗ[K]
      (OddRowTensor K h m b (2*d-b) ⧸
        tensorOddRowRelations hb hbd (fun i => scalarBiformEquiv (h := h) (Q i)) F) :=
  (scalarModulo (K := K)
    (P := Forms K h 0 ⊗[K] Forms K m d)
    (V := Forms K h b ⊗[K] Forms K m (d-b))
    (W := OddRowTensor K h m b (2*d-b))
    (U := (Fin f → Forms K h (b-1) ⊗[K] Forms K m (d-b+1)) ×
      (Fin q → Forms K h b ⊗[K] Forms K m (d-b)))
    (oddTensorRowMap hb hbd (fun i => scalarBiformEquiv (h := h) (Q i)) F)
    (oddRowScalarAction hbd)).comp scalarBiformEquiv.toLinearMap

@[simp] theorem oddActualRowScalarAction_apply (hb : 1 ≤ b) (hbd : b ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K m d) (v : Forms K h b ⊗[K] Forms K m (d-b)) :
    oddActualRowScalarAction hb hbd Q F p v=
      (tensorOddRowRelations hb hbd (fun i => scalarBiformEquiv (h := h) (Q i)) F).mkQ
        (oddRowScalarAction hbd (scalarBiformEquiv (h := h) p) v) := rfl

theorem oddActualRowScalarAction_growth (hb : 1 ≤ b) (hbd : b ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (t : ℕ) (hg : OddScalarLayerProperty t hb hbd
      (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (L : Submodule K (Forms K h b ⊗[K] Forms K m (d-b))) :
    t*finrank K L≤finrank K (BilinearImage.image
      (K := K) (F := Forms K m d)
      (V := Forms K h b ⊗[K] Forms K m (d-b))
      (W := OddRowTensor K h m b (2*d-b) ⧸
        tensorOddRowRelations hb hbd (fun i => scalarBiformEquiv (h := h) (Q i)) F)
      (oddActualRowScalarAction hb hbd Q F) L) := by
  unfold oddActualRowScalarAction
  rw [bilinearImage_parameter_surjective _ scalarBiformEquiv.toLinearMap scalarBiformEquiv.surjective]
  exact hg.2 L

end Froberg
