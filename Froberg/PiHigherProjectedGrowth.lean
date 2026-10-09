module

public import Froberg.PiBilinearGrowth
public import Froberg.ProductCoordinateRank

@[expose] public section

/-! Higher-layer growth in the actual bottom-times-higher source
coordinates, with arbitrary finite labels on the higher blocks. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic
variable {K P V V₀ W I : Type*} [Field K] [Fintype I]
  [AddCommGroup P] [Module K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {Vi Wi : I → Type*}
  [∀ i,AddCommGroup (Vi i)] [∀ i,Module K (Vi i)] [∀ i,FiniteDimensional K (Vi i)]
  [∀ i,AddCommGroup (Wi i)] [∀ i,Module K (Wi i)] [∀ i,FiniteDimensional K (Wi i)]

theorem higher_growth_of_pi_projection
    (eV : V ≃ₗ[K] V₀ × ((i : I) → Vi i))
    (pi : W →ₗ[K] ((i : I) → Wi i))
    (mu : P →ₗ[K] V →ₗ[K] W)
    (diag : (i : I) → P →ₗ[K] Vi i →ₗ[K] Wi i)
    (hdiag : ∀ p v i,pi (mu p v) i=diag i p ((eV v).2 i))
    (rate : ℕ)
    (hgrowth : ∀ i (S : Submodule K (Vi i)),rate*finrank K S ≤
      finrank K (BilinearImage.image (diag i) S))
    (L : Submodule K V) :
    rate*(finrank K L-finrank K (L.comap
      (eV.symm.toLinearMap.comp (LinearMap.inl K V₀ ((i : I) → Vi i))))) ≤
      finrank K (BilinearImage.image mu L) := by
  let pr := (LinearMap.snd K V₀ ((i : I) → Vi i)).comp eV.toLinearMap
  have he : mu.compr₂ₛₗ pi=(piBilinear diag).compl₂ pr := by
    ext p v i
    exact hdiag p v i
  have hi := congrArg (fun f => BilinearImage.image f L) he
  rw [bilinearImage_postcompose,bilinearImage_precompose] at hi
  have hg := piBilinear_growth diag rate hgrowth (L.map pr)
  have hr := coordinates_higher_finrank eV L
  change finrank K (L.map pr)=_ at hr
  rw [hr,←hi] at hg
  exact hg.trans (Submodule.finrank_map_le _ _)

variable {W₀ : Type*} [AddCommGroup W₀] [Module K W₀]

theorem pi_bottom_kernel_eq
    (eV : V ≃ₗ[K] V₀ × ((i : I) → Vi i))
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] V₀ →ₗ[K] W₀)
    (ell : W →ₗ[K] K) (ell₀ : W₀ →ₗ[K] K)
    (hbottom : ∀ p x,ell (mu p (eV.symm (x,0)))=ell₀ (nu p x)) :
    (QuotientCovectorKernel.relation mu ell).ker.comap
      (eV.symm.toLinearMap.comp (LinearMap.inl K V₀ ((i : I) → Vi i)))=
      (QuotientCovectorKernel.relation nu ell₀).ker := by
  ext x
  constructor
  · intro hx
    apply LinearMap.ext
    intro p
    change ell₀ (nu p x)=0
    rw [←hbottom]
    exact LinearMap.congr_fun hx p
  · intro hx
    apply LinearMap.ext
    intro p
    change ell (mu p (eV.symm (x,0)))=0
    rw [hbottom]
    exact LinearMap.congr_fun hx p

theorem pi_bottom_kernel_finrank_le
    (eV : V ≃ₗ[K] V₀ × ((i : I) → Vi i))
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] V₀ →ₗ[K] W₀)
    (ell : W →ₗ[K] K) (ell₀ : W₀ →ₗ[K] K)
    (hbottom : ∀ p x,ell (mu p (eV.symm (x,0)))=ell₀ (nu p x)) :
    finrank K (QuotientCovectorKernel.relation nu ell₀).ker ≤
      finrank K (QuotientCovectorKernel.relation mu ell).ker := by
  let f := eV.symm.toLinearMap.comp (LinearMap.inl K V₀ ((i : I) → Vi i))
  have hf : Function.Injective f := by
    intro x y hxy
    exact congrArg Prod.fst (eV.symm.injective hxy)
  rw [←pi_bottom_kernel_eq eV mu nu ell ell₀ hbottom]
  change finrank K ((QuotientCovectorKernel.relation mu ell).ker.comap f) ≤ _
  rw [(Submodule.equivMapOfInjective f hf _).finrank_eq]
  exact Submodule.finrank_mono (Submodule.map_comap_le _ _)

end Froberg
