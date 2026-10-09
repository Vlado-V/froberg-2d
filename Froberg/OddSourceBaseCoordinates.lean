module

public import Froberg.OddBiformDecomposition
public import Froberg.SourceCoordinateTools

@[expose] public section

/-! Explicit odd source coordinates after quotienting by the linear outer
generators. Every higher odd coefficient block is retained unchanged. -/
noncomputable section
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d f : ℕ}

abbrev OddBottomTensor (K : Type) [Field K] (h m d : ℕ) :=
  Forms K h 1 ⊗[K] Forms K m (d-1)

instance oddBottomTensorGroup (K : Type) [Field K] (h m d : ℕ) :
    AddCommGroup (OddBottomTensor K h m d) := tensorFormGroup

instance oddBottomTensorModule (K : Type) [Field K] (h m d : ℕ) :
    Module K (OddBottomTensor K h m d) := TensorProduct.leftModule

def oddBottomIndex (hd : 1≤d) : Fin ((d+1)/2) := ⟨0,by omega⟩

abbrev HigherOddCoordinates (K : Type) [Field K] (h m d : ℕ) (hd : 1≤d) :=
  (r : {r : Fin ((d+1)/2) // r≠oddBottomIndex hd}) →
    Forms K h (2*r.val.val+1) ⊗[K] Forms K m (d-(2*r.val.val+1))

instance higherOddCoordinatesGroup (K : Type) [Field K] (h m d : ℕ) (hd : 1≤d) :
    AddCommGroup (HigherOddCoordinates K h m d hd) :=
  Pi.addCommGroup

instance higherOddCoordinatesModule (K : Type) [Field K] (h m d : ℕ) (hd : 1≤d) :
    Module K (HigherOddCoordinates K h m d hd) :=
  Pi.module _ _ K

def oddSplitCoordinates (hd : 1≤d) : biformParitySpace K h m d 1 ≃ₗ[K]
    (Forms K h 1 ⊗[K] Forms K m (d-1)) × HigherOddCoordinates K h m d hd :=
  (oddBiformCoordinatesEquiv (K := K) (h := h) (m := m) (d := d)).trans
    (piSplitAtLinear (K := K)
      (fun r : Fin ((d+1)/2) => Forms K h (2*r.val+1) ⊗[K] Forms K m (d-(2*r.val+1)))
      (oddBottomIndex hd))

theorem oddSplitCoordinates_bottom (hd : 1≤d)
    (v : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    oddSplitCoordinates hd (oddBiformEmbedding (t := 1) hd (by decide) v)=(v,0) := by
  have hw : (sumBiformMap v).IsWeightedHomogeneous (blockWeight h m) 1 :=
    biformImage_output_weight (Forms K h 1) (Forms K m (d-1)) le_rfl
      (sumBiformMap_range.le ⟨v,rfl⟩)
  apply Prod.ext
  · apply sumBiformMap_injective
    change sumBiformMap (oddBiformCoordinatesEquiv
      (oddBiformEmbedding (t := 1) hd (by decide) v) (oddBottomIndex hd))=sumBiformMap v
    rw [oddBiformCoordinatesEquiv_component,oddBiformEmbedding_val]
    exact hw.weightedHomogeneousComponent_same
  · funext r
    apply sumBiformMap_injective
    change sumBiformMap (oddBiformCoordinatesEquiv
      (oddBiformEmbedding (t := 1) hd (by decide) v) r.val)=sumBiformMap 0
    rw [oddBiformCoordinatesEquiv_component,oddBiformEmbedding_val,map_zero]
    apply hw.weightedHomogeneousComponent_ne
    intro he
    apply r.property
    apply Fin.ext
    change r.val.val=0
    omega

theorem oddSplitCoordinates_outer_relations (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (Submodule.span K (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i)))).map
      (oddSplitCoordinates hd).toLinearMap=
    (Submodule.span K (Set.range F)).map
      (LinearMap.inl K (Forms K h 1 ⊗[K] Forms K m (d-1)) (HigherOddCoordinates K h m d hd)) := by
  rw [Submodule.map_span,Submodule.map_span,←Set.range_comp',←Set.range_comp']
  congr 1
  apply congrArg Set.range
  funext i
  exact oddSplitCoordinates_bottom hd (F i)

def oddSourceBaseEquiv (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (biformParitySpace K h m d 1 ⧸ Submodule.span K
      (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i)))) ≃ₗ[K]
    (OddBottomTensor K h m d ⧸ Submodule.span K (Set.range F)) ×
      HigherOddCoordinates K h m d hd :=
  (Submodule.Quotient.equiv _ _ (oddSplitCoordinates (K := K) (h := h) (m := m) hd)
    (oddSplitCoordinates_outer_relations hd F)).trans
      (productLeftQuotientEquiv (K := K) (X := OddBottomTensor K h m d)
        (Y := HigherOddCoordinates K h m d hd) (Submodule.span K (Set.range F)))

@[simp] theorem oddSourceBaseEquiv_mk (hd : 1≤d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) (p : biformParitySpace K h m d 1) :
    oddSourceBaseEquiv hd F ((Submodule.span K
      (Set.range (fun i => oddBiformEmbedding (t := 1) hd (by decide) (F i)))).mkQ p)=
      ((Submodule.span K (Set.range F)).mkQ (oddSplitCoordinates hd p).1,
        (oddSplitCoordinates hd p).2) := rfl

end Froberg
