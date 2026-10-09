module

public import Froberg.HigherBlockGrowth
public import Froberg.BilinearPostcompose
public import Quartic.QuotientCovectorKernel

@[expose] public section

/-! Uniform higher-layer growth is preserved by an actual target
projection and arbitrary coordinates on the coefficient source. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Quartic Quartic.FilteredImage
variable {K P V V' W : Type*} [Field K]
  [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module K W]

theorem bilinearImage_precompose (mu : P →ₗ[K] V →ₗ[K] W)
    (g : V' →ₗ[K] V) (L : Submodule K V') :
    BilinearImage.image (mu.compl₂ g) L=BilinearImage.image mu (L.map g) := by
  simp only [BilinearImage.image]
  congr 1
  funext p
  rw [←Submodule.map_comp]
  rfl

variable {n : ℕ} {Vi Wi : Fin (n+1) → Type*}
  [∀ i,AddCommGroup (Vi i)] [∀ i,Module K (Vi i)]
  [∀ i,FiniteDimensional K (Vi i)]
  [∀ i,AddCommGroup (Wi i)] [∀ i,Module K (Wi i)]
  [∀ i,FiniteDimensional K (Wi i)]
  [FiniteDimensional K V] [FiniteDimensional K W]

theorem higher_growth_of_block_projection
    (eV : V ≃ₗ[K] ((i : Fin (n+1)) → Vi i))
    (pi : W →ₗ[K] ((i : Fin (n+1)) → Wi i))
    (mu : P →ₗ[K] V →ₗ[K] W)
    (diag : (i : Fin (n+1)) → P →ₗ[K] Vi i →ₗ[K] Wi i)
    (hdiag : ∀ p v,pi (mu p v)=blockBilinear diag p (eV v))
    (rate : ℕ)
    (hgrowth : ∀ i : Fin n,∀ S : Submodule K (Vi i.succ),rate*finrank K S ≤
      finrank K (BilinearImage.image (diag i.succ) S))
    (L : Submodule K V) :
    rate*(finrank K L-finrank K (initialPiece Vi (L.map eV.toLinearMap) 0)) ≤
      finrank K (BilinearImage.image mu L) := by
  have he : blockBilinear diag=(mu.compl₂ eV.symm.toLinearMap).compr₂ₛₗ pi := by
    apply LinearMap.ext
    intro p
    apply LinearMap.ext
    intro v
    change blockBilinear diag p v=pi (mu p (eV.symm v))
    simpa only [LinearEquiv.apply_symm_apply] using (hdiag p (eV.symm v)).symm
  have hi : BilinearImage.image (blockBilinear diag) (L.map eV.toLinearMap)=
      (BilinearImage.image mu L).map pi := by
    rw [he,bilinearImage_postcompose,bilinearImage_precompose,←Submodule.map_comp]
    simp only [LinearEquiv.symm_comp,Submodule.map_id]
  have hg := blockBilinear_higher_growth diag rate hgrowth (L.map eV.toLinearMap)
  rw [eV.finrank_map_eq,hi] at hg
  exact hg.trans (Submodule.finrank_map_le _ _)


theorem initialPiece_zero_eq_comap
    (eV : V ≃ₗ[K] ((i : Fin (n+1)) → Vi i)) (L : Submodule K V) :
    initialPiece Vi (L.map eV.toLinearMap) 0=
      L.comap (eV.symm.toLinearMap.comp (LinearMap.single K Vi 0)) := by
  ext x
  constructor
  · rintro ⟨v,⟨hv,hprefix⟩,hvx⟩
    change v 0=x at hvx
    change ∀ i : Fin (n+1),1 ≤ i.val → v i=0 at hprefix
    have he : v=Pi.single 0 x := by
      funext i
      by_cases hi : i=0
      · subst i
        simpa only [Pi.single_eq_same] using hvx
      · rw [Pi.single_eq_of_ne hi]
        apply hprefix i
        have hiv : i.val≠0 := by intro hz; apply hi; exact Fin.ext hz
        omega
    obtain ⟨y,hy,hyv⟩ := hv
    change eV y=v at hyv
    change eV.symm (Pi.single 0 x)∈L
    rw [←he,←hyv,eV.symm_apply_apply]
    exact hy
  · intro hx
    refine ⟨Pi.single 0 x,⟨?_,?_⟩,?_⟩
    · exact ⟨eV.symm (Pi.single 0 x),hx,eV.apply_symm_apply _⟩
    · intro i hi
      change 1 ≤ i.val at hi
      change (Pi.single 0 x : (i : Fin (n+1)) → Vi i) i=0
      simp only [Pi.single_eq_of_ne (show i≠0 from by intro he; subst i; simp at hi)]
    · exact Pi.single_eq_same 0 x

variable {W0 : Type*} [AddCommGroup W0] [Module K W0]

theorem kernel_initialPiece_zero
    (eV : V ≃ₗ[K] ((i : Fin (n+1)) → Vi i))
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] Vi 0 →ₗ[K] W0)
    (ell : W →ₗ[K] K) (ell0 : W0 →ₗ[K] K)
    (hbottom : ∀ p x,ell (mu p (eV.symm (Pi.single 0 x)))=ell0 (nu p x)) :
    initialPiece Vi ((QuotientCovectorKernel.relation mu ell).ker.map eV.toLinearMap) 0=
      (QuotientCovectorKernel.relation nu ell0).ker := by
  rw [initialPiece_zero_eq_comap]
  ext x
  constructor
  · intro hx
    apply LinearMap.ext
    intro p
    change ell0 (nu p x)=0
    rw [←hbottom]
    exact LinearMap.congr_fun hx p
  · intro hx
    apply LinearMap.ext
    intro p
    change ell (mu p (eV.symm (Pi.single 0 x)))=0
    rw [hbottom]
    exact LinearMap.congr_fun hx p


theorem bottom_kernel_finrank_le
    (eV : V ≃ₗ[K] ((i : Fin (n+1)) → Vi i))
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] Vi 0 →ₗ[K] W0)
    (ell : W →ₗ[K] K) (ell0 : W0 →ₗ[K] K)
    (hbottom : ∀ p x,ell (mu p (eV.symm (Pi.single 0 x)))=ell0 (nu p x)) :
    finrank K (QuotientCovectorKernel.relation nu ell0).ker ≤
      finrank K (QuotientCovectorKernel.relation mu ell).ker := by
  rw [←kernel_initialPiece_zero eV mu nu ell ell0 hbottom]
  unfold initialPiece
  calc
    _ ≤ finrank K ↥(((QuotientCovectorKernel.relation mu ell).ker.map eV.toLinearMap) ⊓
      coordinateFlag Vi ((0 : Fin (n+1)).val+1)) := Submodule.finrank_map_le _ _
    _ ≤ finrank K ((QuotientCovectorKernel.relation mu ell).ker.map eV.toLinearMap) :=
      Submodule.finrank_mono inf_le_left
    _ = _ := eV.finrank_map_eq _

end Froberg
