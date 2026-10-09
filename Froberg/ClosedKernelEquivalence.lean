module

public import Froberg.ActualSliceVectors

@[expose] public section

/-! Closed kernel slices transport under actual bilinear equivalences.
The auxiliary cuts are transported as target vectors. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg.BilinearScalarFamily
open Module Quartic
variable {K P V W P' V' W' : Type*} [Field K]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup P'] [Module K P'] [FiniteDimensional K P']
  [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']

 theorem relation_kernel_equivalence
    (eP : P ≃ₗ[K] P') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P' →ₗ[K] V' →ₗ[K] W')
    (hmu : ∀ p v,eW (mu p v)=nu (eP p) (eV v)) (ell : W' →ₗ[K] K) :
    (QuotientCovectorKernel.relation nu ell).ker=
      (QuotientCovectorKernel.relation mu (ell.comp eW.toLinearMap)).ker.map eV.toLinearMap := by
  ext v
  constructor
  · intro hv
    refine ⟨eV.symm v,?_,eV.apply_symm_apply v⟩
    apply LinearMap.ext
    intro p
    change ell (eW (mu p (eV.symm v)))=0
    rw [hmu,LinearEquiv.apply_symm_apply]
    exact DFunLike.congr_fun hv (eP p)
  · rintro ⟨v,hv,rfl⟩
    apply LinearMap.ext
    intro p
    obtain ⟨p,rfl⟩ := eP.surjective p
    change ell (nu (eP p) (eV v))=0
    rw [←hmu]
    exact DFunLike.congr_fun hv p

theorem relation_kernel_finrank_equivalence
    (eP : P ≃ₗ[K] P') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P' →ₗ[K] V' →ₗ[K] W')
    (hmu : ∀ p v,eW (mu p v)=nu (eP p) (eV v)) (ell : W' →ₗ[K] K) :
    finrank K (QuotientCovectorKernel.relation nu ell).ker=
      finrank K (QuotientCovectorKernel.relation mu (ell.comp eW.toLinearMap)).ker := by
  rw [relation_kernel_equivalence eP eV eW mu nu hmu ell,LinearEquiv.finrank_map_eq]

theorem HasClosedKernelSlices.equiv
    (eP : P ≃ₗ[K] P') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P' →ₗ[K] V' →ₗ[K] W')
    (hmu : ∀ p v,eW (mu p v)=nu (eP p) (eV v)) (s : ℕ → ℕ)
    (hs : HasClosedKernelSlices mu s) : HasClosedKernelSlices nu s := by
  obtain ⟨Z,hZ⟩ := (hasClosedKernelSlices_iff_vectors mu s).mp hs
  have hdim : finrank K V=finrank K V' := eV.finrank_eq
  let oldIndex (r : Fin (finrank K V'+1)) : Fin (finrank K V+1) :=
    ⟨r.val,by rw [hdim];exact r.isLt⟩
  apply (hasClosedKernelSlices_iff_vectors nu s).mpr
  refine ⟨fun r i => eW (Z (oldIndex r) i),?_⟩
  intro r ell hr hcuts
  have hk := relation_kernel_finrank_equivalence eP eV eW mu nu hmu ell
  have hz : ell.comp eW.toLinearMap=0 := hZ (oldIndex r) (ell.comp eW.toLinearMap)
    (hr.trans_eq hk) hcuts
  apply LinearMap.ext
  intro w
  obtain ⟨w,rfl⟩ := eW.surjective w
  exact DFunLike.congr_fun hz w

end Froberg.BilinearScalarFamily
