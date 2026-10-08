import Froberg.HigherProjectedGrowth

/-! Uniform diagonal growth for any finite family of coefficient blocks.
Only an enumeration is used in the proof; the interface keeps the actual
index type and its dependent spaces. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module Quartic Quartic.FilteredImage
variable {K P I : Type*} [Field K] [AddCommGroup P] [Module K P] [Fintype I]
variable {V W : I → Type*}
  [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  [∀ i,AddCommGroup (W i)] [∀ i,Module K (W i)]

def piBilinear (mu : (i : I) → P →ₗ[K] V i →ₗ[K] W i) :
    P →ₗ[K] ((i : I) → V i) →ₗ[K] ((i : I) → W i) where
  toFun p := LinearMap.pi fun i => (mu i p).comp (LinearMap.proj i)
  map_add' p q := by ext v i;simp
  map_smul' c p := by ext v i;simp

@[simp] theorem piBilinear_apply (mu : (i : I) → P →ₗ[K] V i →ₗ[K] W i)
    (p : P) (v : (i : I) → V i) (i : I) : piBilinear mu p v i=mu i p (v i) := rfl

theorem piBilinear_growth [∀ i,FiniteDimensional K (V i)] [∀ i,FiniteDimensional K (W i)]
    (mu : (i : I) → P →ₗ[K] V i →ₗ[K] W i) (rate : ℕ)
    (hmu : ∀ i (S : Submodule K (V i)),rate*finrank K S ≤
      finrank K (BilinearImage.image (mu i) S))
    (L : Submodule K ((i : I) → V i)) :
    rate*finrank K L ≤ finrank K (BilinearImage.image (piBilinear mu) L) := by
  classical
  let e := Fintype.equivFin I
  let eV := LinearEquiv.piCongrLeft' K V e
  let eW := LinearEquiv.piCongrLeft' K W e
  let nu := fun i : Fin (Fintype.card I) => mu (e.symm i)
  have he : (piBilinear mu).compr₂ₛₗ eW.toLinearMap=
      (blockBilinear nu).compl₂ eV.toLinearMap := by
    ext p v i
    rfl
  have himg := congrArg (fun z => BilinearImage.image z L) he
  rw [bilinearImage_postcompose,bilinearImage_precompose] at himg
  have hg := blockBilinear_weighted_growth nu (fun _ => rate)
    (fun i S => hmu (e.symm i) S) (L.map eV.toLinearMap)
  rw [←Finset.mul_sum,sum_initialPiece_finrank,←himg,eW.finrank_map_eq,eV.finrank_map_eq] at hg
  exact hg

end Froberg
