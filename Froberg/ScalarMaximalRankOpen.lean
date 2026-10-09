module

public import Froberg.ScalarMaximalRank

@[expose] public section

/-! The strict-shadow criterion gives an actual scalar family of maximal
rank for every number of scalar forms. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem generic_scalar_maximal_rank (mu : F →ₗ[K] V →ₗ[K] W) (q : ℕ) (D : ℝ)
    (hA : 0 < finrank K V) (hD : (finrank K V : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K V,
      ((finrank K W : ℝ)/finrank K V)*finrank K L+
        D*(min (finrank K L) (finrank K V-finrank K L) : ℕ) ≤
        finrank K (Quartic.BilinearImage.image mu L)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → F))) K,
      (∃ Q : Fin q → F,eval (coordinates K (Fin q → F) Q) P ≠ 0) ∧
      ∀ Q : Fin q → F,eval (coordinates K (Fin q → F) Q) P ≠ 0 →
        finrank K (multiplication mu Q).range = min (q*finrank K V) (finrank K W) := by
  classical
  obtain ⟨Q₀,hQ₀⟩ := exists_scalar_maximal_rank mu q D hA hD hgrowth
  let decode := (coordinates K (Fin q → F)).symm.toLinearMap
  let A := (tupleBilinear mu).flip.comp decode
  have hpoly := Quartic.isPolynomialFamily_linear A
  obtain ⟨P,hP,hgood⟩ := Quartic.rank_polynomial_principal_open A hpoly
    (coordinates K (Fin q → F) Q₀)
  have heval (Q : Fin q → F) : A (coordinates K (Fin q → F) Q)=multiplication mu Q := by
    simp only [A,decode,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨P,⟨Q₀,hP⟩,?_⟩
  intro Q hQ
  have hlo := hgood (coordinates K (Fin q → F) Q) hQ
  rw [heval,heval,hQ₀] at hlo
  apply Nat.le_antisymm _ hlo
  apply le_min
  · have hd := (multiplication mu Q).finrank_range_le
    simpa [Module.finrank_pi_fintype] using hd
  · exact Submodule.finrank_le _

end Froberg.BilinearScalarFamily
