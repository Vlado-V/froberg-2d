module

public import Froberg.OddBackgroundBlocks

@[expose] public section

/-! Tensor coordinates for one literal output-degree component, in any
parity. The coordinate map is onto precisely when the output degree has
the prescribed parity. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d t : ℕ} {p : ZMod 2}

def biformTensorComponent (ht : t ≤ d) :
    biformParitySpace K h m d p →ₗ[K]
      Forms K h t ⊗[K] Forms K m (d-t) :=
  (LinearEquiv.ofInjective (sumBiformMap (K := K) (h := h) (n := m)
    (a := t) (c := d-t)) sumBiformMap_injective).symm.toLinearMap.comp
    (((weightedHomogeneousComponent (blockWeight h m) t).comp
      (biformParitySpace K h m d p).subtype).codRestrict _ (by
        intro v
        change ∃ z, sumBiformMap z=weightedHomogeneousComponent (blockWeight h m) t v.val
        apply exists_sumBiformMap_of_homogeneous
        · simpa only [Nat.add_sub_of_le ht] using
            weightedComponent_preserves_homogeneous (blockWeight h m) v.property.1 t
        · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _))

@[simp] theorem biformTensorComponent_spec (ht : t ≤ d)
    (v : biformParitySpace K h m d p) :
    sumBiformMap (biformTensorComponent ht v)=
      weightedHomogeneousComponent (blockWeight h m) t v.val := by
  change (LinearEquiv.ofInjective (sumBiformMap (K := K) (h := h) (n := m)
    (a := t) (c := d-t)) sumBiformMap_injective
      ((LinearEquiv.ofInjective _ sumBiformMap_injective).symm _)).val=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem biformTensorComponent_even (ht : t ≤ d) (he : t%2=0)
    (v : Forms K h t ⊗[K] Forms K m (d-t)) :
    biformTensorComponent ht (evenBiformEmbedding ht he v)=v := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,evenBiformEmbedding_val]
  exact (biformImage_output_weight (Forms K h t) (Forms K m (d-t)) le_rfl
    (sumBiformMap_range.le ⟨v,rfl⟩)).weightedHomogeneousComponent_same

theorem biformTensorComponent_odd (ht : t ≤ d) (ho : t%2=1)
    (v : Forms K h t ⊗[K] Forms K m (d-t)) :
    biformTensorComponent ht (oddBiformEmbedding ht ho v)=v := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,oddBiformEmbedding_val]
  exact (biformImage_output_weight (Forms K h t) (Forms K m (d-t)) le_rfl
    (sumBiformMap_range.le ⟨v,rfl⟩)).weightedHomogeneousComponent_same

theorem biformTensorComponent_even_surjective (ht : t ≤ d) (he : t%2=0) :
    Function.Surjective (biformTensorComponent (K := K) (h := h) (m := m) (p := 0) ht) :=
  fun v => ⟨evenBiformEmbedding ht he v,biformTensorComponent_even ht he v⟩

theorem biformTensorComponent_odd_surjective (ht : t ≤ d) (ho : t%2=1) :
    Function.Surjective (biformTensorComponent (K := K) (h := h) (m := m) (p := 1) ht) :=
  fun v => ⟨oddBiformEmbedding ht ho v,biformTensorComponent_odd ht ho v⟩

theorem biformTensorComponent_eq_oddCoordinates (v : biformParitySpace K h m d 1)
    (r : Fin ((d+1)/2)) :
    biformTensorComponent (by omega : 2*r.val+1 ≤ d) v=oddBiformCoordinatesEquiv v r := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,oddBiformCoordinatesEquiv_component]

end Froberg
