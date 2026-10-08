import Froberg.EvenHigherGrowth
import Froberg.BottomVectorSlices

/-! The even-case bottom row is exactly the checked B.3 vector quotient,
including its actual scalar multiplication. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic VectorMultiplicationCoordinates
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable (hdp : 1≤d) (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1))
local notation "F" => bottomTensorFamily g
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)
local notation "eW" => oddTargetBaseEquiv hdp Q₀ F₁ hQ₀ hF₁
local notation "eV" => oddSourceBaseEquiv hdp F

theorem evenBackgroundScalar_bottom (p : Forms K m d) (x : OddBottomQuotient F) :
    eW (evenBackgroundScalar hdp Q F p ((eV).symm (x,0)))=
      (bottomCoordinateScalarAction hdp Q g p x,0) := by
  obtain ⟨v,rfl⟩ := (Submodule.span K (Set.range F)).mkQ_surjective x
  have he : (eV).symm ((Submodule.span K (Set.range F)).mkQ v,0)=
      (Submodule.span K (Set.range F₁)).mkQ (oddBiformEmbedding hdp (by decide) v) := by
    apply (eV).injective
    rw [LinearEquiv.apply_symm_apply,oddSourceBaseEquiv_mk,oddSplitCoordinates_bottom]
  rw [he,evenBackgroundScalar_mk]
  change oddTargetBaseMap hdp Q₀ F₁ hQ₀ hF₁
    (evenScalarOddProduct (scalarEvenBiform p) (oddBiformEmbedding hdp (by decide) v))=_
  apply Prod.ext
  · rw [bottomCoordinateScalarAction_mk,oddTargetBaseMap_bottom]
    congr 1
    rw [←biformTensorComponent_eq_oddCoordinates]
    change biformTensorComponent (by omega : 1≤2*d)
      (evenScalarOddProduct (evenBiformEmbedding (Nat.zero_le d) (by decide) (scalarBiformEquiv p))
        (oddBiformEmbedding hdp (by decide) v))=_
    rw [biformTensorComponent_scalar_product,biformTensorComponent_odd]
  · exact oddTargetBaseMap_bottom_product hdp Q₀ F₁ hQ₀ hF₁
      (scalarEvenBiform p) (scalarEvenBiform_weighted p) _ (oddLinearBiform_weighted hdp v)

end Froberg
