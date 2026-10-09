module

public import Froberg.FramedPreparedParameters

@[expose] public section

/-! Linear extraction of the exact high biform coefficients from the
prepared parameter space. Scalar shifts do not enter these maps. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K] {h m d q j e : ℕ}
attribute [local instance] tensorGroup

theorem biformImage_mono {O O' : Submodule K (Poly K h)}
    {C C' : Submodule K (Poly K m)} (hO : O≤O') (hC : C≤C') :
    biformImage O C≤biformImage O' C' := by
  rintro _ ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change tensorEquivSum K (Fin h) (Fin m) K (a.val ⊗ₜ[K] b.val)∈_
    rw [tensorEquivSum_tmul]
    exact mul_mem_biformImage _ _ (hO a.property) (hC b.property)
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

def constrainedBiformCoordinates (O : Submodule K (Poly K h)) (hO : O≤Forms K h j) :
    biformImage O (Forms K m e) →ₗ[K] Forms K h j ⊗[K] Forms K m e :=
  sumBiformEquiv.symm.toLinearMap.comp
    (Submodule.inclusion (biformImage_mono hO le_rfl))

@[simp] theorem sum_constrainedBiformCoordinates (O : Submodule K (Poly K h))
    (hO : O≤Forms K h j) (v : biformImage O (Forms K m e)) :
    sumBiform (constrainedBiformCoordinates O hO v)=v.val := by
  change (sumBiformEquiv (sumBiformEquiv.symm
    (Submodule.inclusion (biformImage_mono hO le_rfl) v))).val=v.val
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem constrainedBiformCoordinates_framed {H r : ℕ}
    (frame : Fin H → Forms K h j) (c : Fin r → Fin H → Forms K m e) (i : Fin r) :
    constrainedBiformCoordinates (outputFrameSpace frame) (outputFrameSpace_homogeneous frame)
      ⟨sumBiform (framedBiformFamily frame c i),framed_coefficients_mem_prepared frame c i⟩=
      framedBiformFamily frame c i := by
  apply sumBiform_injective
  exact sum_constrainedBiformCoordinates _ _ _

variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def preparedLayerTensor (a : J) (hO : O a.val≤Forms K h a.val) :
    PreparedParameters.Space m d q J counts O →ₗ[K]
      (Fin (counts a.val) → Forms K h a.val ⊗[K] Forms K m (d-a.val)) where
  toFun p i := constrainedBiformCoordinates (O a.val) hO (p.2 a i)
  map_add' p p' := by
    funext i
    exact map_add (constrainedBiformCoordinates (O a.val) hO) (p.2 a i) (p'.2 a i)
  map_smul' c p := by
    funext i
    exact map_smul (constrainedBiformCoordinates (O a.val) hO) c (p.2 a i)

@[simp] theorem preparedLayerTensor_sum (a : J) (hO : O a.val≤Forms K h a.val)
    (p : PreparedParameters.Space m d q J counts O) (i : Fin (counts a.val)) :
    sumBiform (preparedLayerTensor a hO p i)=(p.2 a i).val :=
  sum_constrainedBiformCoordinates (O a.val) hO (p.2 a i)

end Froberg
