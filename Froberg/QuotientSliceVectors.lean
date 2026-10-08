import Froberg.ActualSliceVectors
import Froberg.ScalarQuotientSlices

/-! Lifting and descending actual covector slices through an arbitrary
target quotient, with the source held fixed. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module Quartic QuotientCovectorKernel
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem quotient_slices_iff_lifted (mu : F →ₗ[K] V →ₗ[K] W) (U : Submodule K W) (s : ℕ → ℕ) :
    HasClosedKernelSlices (targetPostcompose mu U.mkQ) s ↔
      ∃ Z : (r : Fin (finrank K V+1)) → Fin (s r.val) → W,
        ∀ r (ell : W →ₗ[K] K),
          r.val ≤ finrank K (LinearMap.ker (relation mu ell)) →
          U ≤ ell.ker → (∀ i,ell (Z r i)=0) → ell=0 := by
  rw [hasClosedKernelSlices_iff_vectors]
  constructor
  · rintro ⟨Z,hZ⟩
    have hx (r : Fin (finrank K V+1)) (i : Fin (s r.val)) := U.mkQ_surjective (Z r i)
    choose Z' hZ' using hx
    refine ⟨Z',?_⟩
    intro r ell hr hU hcuts
    let ellQ := U.liftQ ell hU
    have hrel : relation (targetPostcompose mu U.mkQ) ellQ=relation mu ell := by
      ext v f
      rfl
    have hz : ellQ=0 := hZ r ellQ (by rwa [hrel]) (by
      intro i
      rw [← hZ' r i]
      exact hcuts i)
    exact (descended_eq_zero_iff U ell hU).mp hz
  · rintro ⟨Z,hZ⟩
    refine ⟨fun r i => U.mkQ (Z r i),?_⟩
    intro r ell hr hcuts
    have hz : ell.comp U.mkQ=0 := by
      apply hZ r
      · rwa [relation_targetPostcompose] at hr
      · intro w hw
        change ell (U.mkQ w)=0
        rw [show U.mkQ w=0 from (Submodule.Quotient.mk_eq_zero U).mpr hw,map_zero]
      · exact hcuts
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := U.mkQ_surjective w
    exact DFunLike.congr_fun hz v

end Froberg.BilinearScalarFamily
