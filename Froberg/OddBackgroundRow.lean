module

public import Froberg.BiformTensorComponent
public import Froberg.TwoFamilyIntrinsic

@[expose] public section

/-! The row relations of the actual scalar/linear polynomial background
are exactly the two-family tensor multiplication relations. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d b q f : ℕ}

theorem biformTensorComponent_scalar_product (hb : b ≤ d)
    (Q : Forms K h 0 ⊗[K] Forms K m d) (a : biformParitySpace K h m d 1) :
    biformTensorComponent (by omega : b ≤ 2*d)
      (evenScalarOddProduct (evenBiformEmbedding (t := 0) (Nat.zero_le d) (by decide) Q) a)=
      oddRowScalarAction hb Q (biformTensorComponent hb a) := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec]
  change weightedHomogeneousComponent (blockWeight h m) b (sumBiformMap Q*a.val)=_
  rw [oddRowScalarAction,sumBiformMap_action,biformTensorComponent_spec]
  have hQ : (sumBiformMap Q).IsWeightedHomogeneous (blockWeight h m) 0 :=
    biformImage_output_weight (Forms K h 0) (Forms K m d) le_rfl
      (sumBiformMap_range.le ⟨Q,rfl⟩)
  have he := weighted_component_mul_homogeneous (blockWeight h m) a.val (sumBiformMap Q) b 0 hQ
  simpa only [Nat.add_zero,mul_comm] using he

theorem biformTensorComponent_linear_product (hb : 1 ≤ b) (hbd : b ≤ d)
    (F : Forms K h 1 ⊗[K] Forms K m (d-1)) (a : biformParitySpace K h m d 0) :
    biformTensorComponent (by omega : b ≤ 2*d)
      (oddPrivateProduct (oddBiformEmbedding (t := 1) (by omega) (by decide) F) a)=
      oddRowLinearAction hb hbd F
        (tensorDegreeEquiv (by omega : (b-1)+0=b-1)
          (by omega : (d-(b-1))+0=d-b+1)
          (biformTensorComponent (by omega : b-1 ≤ d) a)) := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec]
  change weightedHomogeneousComponent (blockWeight h m) b (sumBiformMap F*a.val)=_
  rw [oddRowLinearAction,sumBiformMap_action,sumBiformMap_degree_equiv]
  have hs := biformTensorComponent_spec (K := K) (h := h) (m := m) (d := d)
    (p := 0) (t := b-1) (by omega) a
  have hF : (sumBiformMap F).IsWeightedHomogeneous (blockWeight h m) 1 :=
    biformImage_output_weight (Forms K h 1) (Forms K m (d-1)) le_rfl
      (sumBiformMap_range.le ⟨F,rfl⟩)
  have he := weighted_component_mul_homogeneous (blockWeight h m) a.val (sumBiformMap F) (b-1) 1 hF
  calc
    _=sumBiformMap F*weightedHomogeneousComponent (blockWeight h m) (b-1) a.val := by
      simpa only [Nat.sub_add_cancel hb,mul_comm] using he
    _=_ := congrArg (fun z => sumBiformMap F*z) hs.symm


def oddLinearCoefficientProjection (hb : 1 ≤ b) (hbd : b ≤ d) :
    biformParitySpace K h m d 0 →ₗ[K]
      Forms K h (b-1) ⊗[K] Forms K m (d-b+1) :=
  (tensorDegreeEquiv (by omega : (b-1)+0=b-1)
    (by omega : (d-(b-1))+0=d-b+1)).toLinearMap.comp
      (biformTensorComponent (by omega : b-1 ≤ d))

theorem oddLinearCoefficientProjection_surjective (hb : 1 ≤ b) (hbd : b ≤ d)
    (ho : b%2=1) : Function.Surjective
      (oddLinearCoefficientProjection (K := K) (h := h) (m := m) hb hbd) :=
  (tensorDegreeEquiv (by omega : (b-1)+0=b-1)
    (by omega : (d-(b-1))+0=d-b+1)).surjective.comp
      (biformTensorComponent_even_surjective (by omega) (by omega))

def oddRowCoefficientProjection (hb : 1 ≤ b) (hbd : b ≤ d) :
    ((Fin f → biformParitySpace K h m d 0) ×
      (Fin q → biformParitySpace K h m d 1)) →ₗ[K]
    ((Fin f → Forms K h (b-1) ⊗[K] Forms K m (d-b+1)) ×
      (Fin q → Forms K h b ⊗[K] Forms K m (d-b))) :=
  (((oddLinearCoefficientProjection hb hbd).compLeft (Fin f)).comp
    (LinearMap.fst K _ _)).prod
    (((biformTensorComponent hbd).compLeft (Fin q)).comp (LinearMap.snd K _ _))

theorem oddRowCoefficientProjection_surjective (hb : 1 ≤ b) (hbd : b ≤ d)
    (ho : b%2=1) : Function.Surjective
      (oddRowCoefficientProjection (K := K) (h := h) (m := m) (q := q) (f := f) hb hbd) := by
  rintro ⟨x,y⟩
  have hx := fun i => oddLinearCoefficientProjection_surjective (K := K) (h := h)
    (m := m) hb hbd ho (x i)
  have hy := fun i => biformTensorComponent_odd_surjective (K := K) (h := h)
    (m := m) hbd ho (y i)
  choose a ha using hx
  choose c hc using hy
  exact ⟨(a,c),Prod.ext (funext ha) (funext hc)⟩

def oddTensorRowMap (hb : 1 ≤ b) (hbd : b ≤ d)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    ((Fin f → Forms K h (b-1) ⊗[K] Forms K m (d-b+1)) ×
      (Fin q → Forms K h b ⊗[K] Forms K m (d-b))) →ₗ[K]
        (Forms K h b ⊗[K] Forms K m (2*d-b)) :=
  twoFamilyMultiplication (K := K)
    (P₁ := Forms K h 1 ⊗[K] Forms K m (d-1))
    (P₂ := Forms K h 0 ⊗[K] Forms K m d)
    (V₁ := Forms K h (b-1) ⊗[K] Forms K m (d-b+1))
    (V₂ := Forms K h b ⊗[K] Forms K m (d-b))
    (W := Forms K h b ⊗[K] Forms K m (2*d-b))
    (oddRowLinearAction (K := K) (h := h) (n := m) hb hbd)
    (oddRowScalarAction (K := K) (h := h) (n := m) hbd) (F,Q)

theorem oddBackground_row_commutes (hb : 1 ≤ b) (hbd : b ≤ d)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (biformTensorComponent (by omega : b ≤ 2*d)).comp
      ((privateEvenCoefficientMap (fun i => oddBiformEmbedding (by omega) (by decide) (F i))).coprod
        (evenScalarOddFamily (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i)))) =
    (oddTensorRowMap hb hbd Q F).comp
      (oddRowCoefficientProjection hb hbd) := by
  apply LinearMap.ext
  rintro ⟨a,c⟩
  change biformTensorComponent (by omega : b ≤ 2*d)
    (privateEvenCoefficientMap _ a+evenScalarOddFamily _ c)=_
  rw [map_add]
  simp only [privateEvenCoefficientMap,evenScalarOddFamily,LinearMap.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,map_sum]
  simp only [biformTensorComponent_linear_product hb hbd,biformTensorComponent_scalar_product hbd]
  rw [oddTensorRowMap,twoFamilyMultiplication_apply]
  rfl

theorem oddBackground_tensor_row_range (hb : 1 ≤ b) (hbd : b ≤ d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (oddBackgroundRelations
      (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))
      (fun i => oddBiformEmbedding (by omega) (by decide) (F i))).map
        (biformTensorComponent (by omega : b ≤ 2*d))=
    (oddTensorRowMap hb hbd Q F).range := by
  have he := congrArg LinearMap.range (oddBackground_row_commutes hb hbd Q F)
  rw [LinearMap.range_comp,LinearMap.range_coprod,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (oddRowCoefficientProjection_surjective hb hbd ho),
    Submodule.map_top] at he
  simpa only [oddBackgroundRelations,sup_comm] using he

end Froberg
