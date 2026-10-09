module

public import Froberg.OddAmbientRow

@[expose] public section

/-! Intermediate source coordinates descend through the actual F,U+P
relations and commute with scalar multiplication in the ambient quotient. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d b q f u : ℕ}

theorem biformTensorComponent_weight_ne {j : ℕ} (hb : b ≤ d)
    (v : biformParitySpace K h m d 1)
    (hv : v.val.IsWeightedHomogeneous (blockWeight h m) j) (hj : b≠j) :
    biformTensorComponent hb v=0 := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,map_zero]
  exact hv.weightedHomogeneousComponent_ne b hj

def oddIntermediateSourceProjection (hd : Odd d) (hb : 3 ≤ b) (hbd : b<d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations
      (fun i => oddBiformEmbedding (by have := hd.pos; omega) (by decide) (F i))
      (fun i => mixedPureOddGenerator hd (U i) (P i))) →ₗ[K]
        OddRowTensor K h m b (d-b) :=
  (oddBackgroundCoefficientRelations _ _).liftQ (biformTensorComponent (by omega)) (by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      apply biformTensorComponent_weight_ne (by omega) _ _ (by omega : b≠1)
      exact biformImage_output_weight (Forms K h 1) (Forms K m (d-1)) le_rfl
        (sumBiformMap_range.le ⟨F i,rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      apply sumBiformMap_injective
      rw [biformTensorComponent_spec,map_zero]
      exact mixedPureOddGenerator_other hd (by omega) (by omega) (U i) (P i))

@[simp] theorem oddIntermediateSourceProjection_mk (hd : Odd d) (hb : 3 ≤ b) (hbd : b<d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : biformParitySpace K h m d 1) :
    oddIntermediateSourceProjection hd hb hbd F U P
      ((oddBackgroundCoefficientRelations _ _).mkQ v)=biformTensorComponent (by omega) v := rfl

theorem oddIntermediateSourceProjection_scalar (hd : Odd d)
    (hb : 3 ≤ b) (hbd : b<d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K h 0 ⊗[K] Forms K m d)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations
      (fun i => oddBiformEmbedding (by have := hd.pos; omega) (by decide) (F i))
      (fun i => mixedPureOddGenerator hd (U i) (P i))) :
    oddAmbientRowProjection hd hb hbd ho Q F U P
      (oddAmbientScalarProduct
        (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))
        (fun i => oddBiformEmbedding (by have := hd.pos; omega) (by decide) (F i))
        (fun i => mixedPureOddGenerator hd (U i) (P i)) p v)=
      (tensorOddRowRelations (b := b) (by omega) (by omega) Q F).mkQ
        (oddRowScalarAction (b := b) (by omega) p (oddIntermediateSourceProjection hd hb hbd F U P v)) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact oddAmbientRowProjection_scalar hd hb hbd ho Q F U P p v

end Froberg
