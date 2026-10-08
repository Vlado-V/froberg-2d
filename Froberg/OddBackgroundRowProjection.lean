import Froberg.OddBackgroundRow
import Froberg.OddScalarLayers
import Froberg.OddBackgroundProduct

/-! Actual background target projections to the individual tensor
quotients, and transfer of the checked scalar growth to literal products. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d b q f : ℕ}

abbrev OddRowTensor (K : Type) [Field K] (h m x y : ℕ) :=
  Forms K h x ⊗[K] Forms K m y

instance oddRowTensorGroup (K : Type) [Field K] (h m x y : ℕ) :
    AddCommGroup (OddRowTensor K h m x y) := tensorFormGroup

instance oddRowTensorModule (K : Type) [Field K] (h m x y : ℕ) :
    Module K (OddRowTensor K h m x y) := TensorProduct.leftModule

abbrev tensorOddBackgroundRelations (hd : 1 ≤ d)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  oddBackgroundRelations (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))
    (fun i => oddBiformEmbedding hd (by decide) (F i))

abbrev tensorOddRowRelations (hb : 1 ≤ b) (hbd : b ≤ d)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  (oddTensorRowMap hb hbd Q F).range

def oddBackgroundRowProjection (hb : 1 ≤ b) (hbd : b ≤ d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (biformParitySpace K h m (2*d) 1 ⧸ tensorOddBackgroundRelations (by omega) Q F) →ₗ[K]
      ((OddRowTensor K h m b (2*d-b)) ⧸ tensorOddRowRelations hb hbd Q F) :=
  (tensorOddBackgroundRelations (by omega) Q F).liftQ
    ((tensorOddRowRelations hb hbd Q F).mkQ.comp (biformTensorComponent (by omega))) (by
      intro a ha
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (oddBackground_tensor_row_range hb hbd ho Q F).le ⟨a,ha,rfl⟩)

@[simp] theorem oddBackgroundRowProjection_mk (hb : 1 ≤ b) (hbd : b ≤ d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (a : biformParitySpace K h m (2*d) 1) :
    oddBackgroundRowProjection hb hbd ho Q F ((tensorOddBackgroundRelations (by omega) Q F).mkQ a)=
      (tensorOddRowRelations hb hbd Q F).mkQ (biformTensorComponent (by omega) a) := rfl

/-- Literal scalar multiplication of a single source row, modulo all Q/F
relations in the entire odd polynomial target. -/
def oddBackgroundRowScalar (hb : 1 ≤ b) (hbd : b ≤ d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (Forms K h 0 ⊗[K] Forms K m d) →ₗ[K]
      (Forms K h b ⊗[K] Forms K m (d-b)) →ₗ[K]
        (biformParitySpace K h m (2*d) 1 ⧸ tensorOddBackgroundRelations (by omega) Q F) :=
  ((evenOddBiformProduct.comp (evenBiformEmbedding (Nat.zero_le d) (by decide))).compl₂
    (oddBiformEmbedding hbd ho)).compr₂ₛₗ (tensorOddBackgroundRelations (by omega) Q F).mkQ

theorem oddBackgroundRowScalar_projection (hb : 1 ≤ b) (hbd : b ≤ d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (oddBackgroundRowScalar hb hbd ho Q F).compr₂ₛₗ
      (oddBackgroundRowProjection hb hbd ho Q F)=
    scalarModulo (K := K)
      (P := Forms K h 0 ⊗[K] Forms K m d)
      (V := Forms K h b ⊗[K] Forms K m (d-b))
      (W := OddRowTensor K h m b (2*d-b))
      (U := (Fin f → Forms K h (b-1) ⊗[K] Forms K m (d-b+1)) ×
        (Fin q → Forms K h b ⊗[K] Forms K m (d-b)))
      (oddTensorRowMap hb hbd Q F) (oddRowScalarAction hbd) := by
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro v
  change (tensorOddRowRelations hb hbd Q F).mkQ
    (biformTensorComponent (by omega)
      (evenScalarOddProduct (evenBiformEmbedding (Nat.zero_le d) (by decide) p)
        (oddBiformEmbedding hbd ho v)))=_
  rw [biformTensorComponent_scalar_product,biformTensorComponent_odd]
  rfl

theorem oddBackgroundRowScalar_growth (hb : 1 ≤ b) (hbd : b ≤ d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) (t : ℕ)
    (hg : OddScalarLayerProperty t hb hbd (F,Q))
    (L : Submodule K (Forms K h b ⊗[K] Forms K m (d-b))) :
    t*finrank K L ≤ finrank K (Quartic.BilinearImage.image
      (K := K) (F := Forms K h 0 ⊗[K] Forms K m d)
      (V := Forms K h b ⊗[K] Forms K m (d-b))
      (W := biformParitySpace K h m (2*d) 1 ⧸ tensorOddBackgroundRelations (by omega) Q F)
      (oddBackgroundRowScalar hb hbd ho Q F) L) := by
  have hh := hg.2 L
  change t*finrank K L ≤ finrank K (Quartic.BilinearImage.image
    (scalarModulo (K := K) (P := Forms K h 0 ⊗[K] Forms K m d)
      (V := Forms K h b ⊗[K] Forms K m (d-b))
      (W := OddRowTensor K h m b (2*d-b))
      (U := (Fin f → Forms K h (b-1) ⊗[K] Forms K m (d-b+1)) ×
        (Fin q → Forms K h b ⊗[K] Forms K m (d-b)))
      (oddTensorRowMap hb hbd Q F) (oddRowScalarAction hbd)) L) at hh
  rw [←oddBackgroundRowScalar_projection hb hbd ho Q F,bilinearImage_postcompose] at hh
  exact hh.trans (Submodule.finrank_map_le _ _)

end Froberg
