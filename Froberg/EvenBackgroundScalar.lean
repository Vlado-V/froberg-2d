module

public import Froberg.OddActualRowGrowth
public import Froberg.MixedAmbientCorrection

@[expose] public section

/-! Literal scalar multiplication modulo the Q,F background, before the
remaining even generators are added. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

abbrev EvenBackgroundSource (hdp : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  biformParitySpace K h m d 1 ⧸ Submodule.span K
    (Set.range (fun i => oddBiformEmbedding hdp (by decide) (F i)))

abbrev EvenBackgroundTarget (hdp : 1≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  biformParitySpace K h m (2*d) 1 ⧸ oddBackgroundRelations
    (fun i => scalarEvenBiform (h := h) (Q i))
    (fun i => oddBiformEmbedding hdp (by decide) (F i))

def evenBackgroundScalar (hdp : 1≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    Forms K m d →ₗ[K] EvenBackgroundSource hdp F →ₗ[K] EvenBackgroundTarget hdp Q F where
  toFun p := (Submodule.span K
    (Set.range (fun i => oddBiformEmbedding hdp (by decide) (F i)))).liftQ
      ((oddBackgroundRelations
        (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i))).mkQ.comp
          (evenScalarOddProduct (scalarEvenBiform p))) (by
      rw [LinearMap.ker_comp,Submodule.ker_mkQ]
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (show (privateEvenCoefficientMap
        (fun i => oddBiformEmbedding hdp (by decide) (F i))).range≤
          oddBackgroundRelations _ _ from le_sup_right)
        (evenOddBiformProduct_generator_mem _ (scalarEvenBiform p) i))
  map_add' p p' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := (Submodule.span K
      (Set.range (fun i => oddBiformEmbedding hdp (by decide) (F i)))).mkQ_surjective x
    change (oddBackgroundRelations _ _).mkQ
      (evenOddBiformProduct (scalarEvenBiform (p+p')) v)=_
    rw [map_add,map_add,LinearMap.add_apply,map_add]
    rfl
  map_smul' c p := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := (Submodule.span K
      (Set.range (fun i => oddBiformEmbedding hdp (by decide) (F i)))).mkQ_surjective x
    change (oddBackgroundRelations _ _).mkQ
      (evenOddBiformProduct (scalarEvenBiform (c • p)) v)=_
    rw [map_smul,map_smul,LinearMap.smul_apply,map_smul]
    rfl

@[simp] theorem evenBackgroundScalar_mk (hdp : 1≤d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K m d) (v : biformParitySpace K h m d 1) :
    evenBackgroundScalar hdp Q F p
      ((Submodule.span K (Set.range (fun i => oddBiformEmbedding hdp (by decide) (F i)))).mkQ v)=
      (oddBackgroundRelations _ _).mkQ
        (evenScalarOddProduct (scalarEvenBiform p) v) := rfl

theorem evenBackgroundScalar_higher_projection {j : ℕ}
    (hdp : 1≤d) (hj : 1≤j) (hjd : j≤d) (ho : j%2=1)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K m d) (v : biformParitySpace K h m d 1) :
    oddBackgroundRowProjection hj hjd ho (fun i => scalarBiformEquiv (h := h) (Q i)) F
      (evenBackgroundScalar hdp Q F p
        ((Submodule.span K (Set.range (fun i => oddBiformEmbedding hdp (by decide) (F i)))).mkQ v))=
      oddActualRowScalarAction hj hjd Q F p (biformTensorComponent hjd v) := by
  change (tensorOddRowRelations hj hjd (fun i => scalarBiformEquiv (h := h) (Q i)) F).mkQ
    (biformTensorComponent (by omega) (evenScalarOddProduct (scalarEvenBiform p) v))=_
  rw [oddActualRowScalarAction_apply]
  congr 1
  exact biformTensorComponent_scalar_product hjd (scalarBiformEquiv p) v

end Froberg
