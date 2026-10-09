module

public import Quartic.FilteredImage
public import Quartic.BilinearImage

@[expose] public section

/-! Scalar multiplication in ordered source/target layers. The actual image
of a graph subspace contains, in its initial pieces, every diagonal product
image. This supplies independent higher-covector conditions in C.4. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic.FilteredImage
variable {K P : Type*} [Field K] [AddCommGroup P] [Module K P]
variable {n : ℕ} {V W : Fin n → Type*}
  [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  [∀ i,AddCommGroup (W i)] [∀ i,Module K (W i)]

def blockBilinear (mu : (i : Fin n) → P →ₗ[K] V i →ₗ[K] W i) :
    P →ₗ[K] ((i : Fin n) → V i) →ₗ[K] ((i : Fin n) → W i) where
  toFun p := LinearMap.pi fun i => (mu i p).comp (LinearMap.proj i)
  map_add' p q := by ext v i; simp
  map_smul' c p := by ext v i; simp

@[simp] theorem blockBilinear_apply
    (mu : (i : Fin n) → P →ₗ[K] V i →ₗ[K] W i)
    (p : P) (v : (i : Fin n) → V i) (i : Fin n) :
    blockBilinear mu p v i=mu i p (v i) := rfl

/-- Every diagonal image in an initial source piece occurs as an actual
initial target image, even when the original source subspace is a graph. -/
theorem blockBilinear_initial_image
    (mu : (i : Fin n) → P →ₗ[K] V i →ₗ[K] W i)
    (L : Submodule K ((i : Fin n) → V i)) (i : Fin n) :
    Quartic.BilinearImage.image (mu i) (initialPiece V L i) ≤
      initialPiece W (Quartic.BilinearImage.image (blockBilinear mu) L) i := by
  apply iSup_le
  intro p
  rintro z ⟨v,hv,rfl⟩
  obtain ⟨x,hx,hxi⟩ := hv
  change x i=v at hxi
  refine ⟨blockBilinear mu p x,⟨?_,?_⟩,?_⟩
  · exact Quartic.BilinearImage.product_mem (blockBilinear mu) L p x hx.1
  · intro j hj
    simp only [blockBilinear_apply,hx.2 j hj,map_zero]
  · change mu i p (x i)=mu i p v
    rw [hxi]

/-- The higher-layer condition ranks add: their coefficient blocks have
distinct leading target degrees. -/
theorem blockBilinear_image_finrank [∀ i,FiniteDimensional K (W i)]
    (mu : (i : Fin n) → P →ₗ[K] V i →ₗ[K] W i)
    (L : Submodule K ((i : Fin n) → V i)) :
    (∑ i,finrank K (Quartic.BilinearImage.image (mu i) (initialPiece V L i))) ≤
      finrank K (Quartic.BilinearImage.image (blockBilinear mu) L) := by
  calc
    _ ≤ ∑ i,finrank K (initialPiece W
        (Quartic.BilinearImage.image (blockBilinear mu) L) i) := by
      exact Finset.sum_le_sum (fun i _ => Submodule.finrank_mono (blockBilinear_initial_image mu L i))
    _ = _ := sum_initialPiece_finrank W _

theorem blockBilinear_weighted_growth [∀ i,FiniteDimensional K (V i)]
    [∀ i,FiniteDimensional K (W i)]
    (mu : (i : Fin n) → P →ₗ[K] V i →ₗ[K] W i) (rate : Fin n → ℕ)
    (hmu : ∀ i (S : Submodule K (V i)),rate i*finrank K S≤
      finrank K (Quartic.BilinearImage.image (mu i) S))
    (L : Submodule K ((i : Fin n) → V i)) :
    (∑ i,rate i*finrank K (initialPiece V L i)) ≤
      finrank K (Quartic.BilinearImage.image (blockBilinear mu) L) :=
  (Finset.sum_le_sum (fun i _ => hmu i _)).trans (blockBilinear_image_finrank mu L)

end Froberg
