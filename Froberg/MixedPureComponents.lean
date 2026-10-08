import Froberg.OddBackgroundQuotient
import Froberg.WeightedRename

/-! Exact components of a mixed pure generator U+P. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d t : ℕ}

theorem pureOutput_weighted (U : Forms K h d) :
    (rename (Sum.inl : Fin h → Fin h ⊕ Fin m) U.val).IsWeightedHomogeneous (blockWeight h m) d := by
  apply weighted_homogeneous_rename ⟨Sum.inl,Sum.inl_injective⟩ (blockWeight h m) U.val d
  exact U.property

theorem linearOutput_weighted (P : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (sumBiformMap P).IsWeightedHomogeneous (blockWeight h m) 1 :=
  biformImage_output_weight (Forms K h 1) (Forms K m (d-1)) le_rfl
    (sumBiformMap_range.le ⟨P,rfl⟩)

theorem mixedPureOddGenerator_top (hd : Odd d) (hd1 : 1<d) (U : Forms K h d)
    (P : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    weightedHomogeneousComponent (blockWeight h m) d (mixedPureOddGenerator hd U P).val=
      rename Sum.inl U.val := by
  rw [mixedPureOddGenerator_val,map_add,(pureOutput_weighted U).weightedHomogeneousComponent_same,
    (linearOutput_weighted P).weightedHomogeneousComponent_ne d (by omega),add_zero]

theorem mixedPureOddGenerator_bottom (hd : Odd d) (hd1 : 1<d) (U : Forms K h d)
    (P : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    weightedHomogeneousComponent (blockWeight h m) 1 (mixedPureOddGenerator hd U P).val=
      sumBiformMap P := by
  rw [mixedPureOddGenerator_val,map_add,
    (pureOutput_weighted U).weightedHomogeneousComponent_ne 1 (by omega),
    (linearOutput_weighted P).weightedHomogeneousComponent_same,zero_add]

theorem mixedPureOddGenerator_other (hd : Odd d) (ht1 : t≠1) (htd : t≠d)
    (U : Forms K h d) (P : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    weightedHomogeneousComponent (blockWeight h m) t (mixedPureOddGenerator hd U P).val=0 := by
  rw [mixedPureOddGenerator_val,map_add,
    (pureOutput_weighted U).weightedHomogeneousComponent_ne t htd,
    (linearOutput_weighted P).weightedHomogeneousComponent_ne t ht1,add_zero]

end Froberg
