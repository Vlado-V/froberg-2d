import Froberg.BilinearScalarSurjection

/-! The strict-shadow criterion gives an actual scalar family of maximal
rank for every number of scalar forms. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_scalar_maximal_rank (mu : F →ₗ[K] V →ₗ[K] W) (q : ℕ) (D : ℝ)
    (hA : 0 < finrank K V) (hD : (finrank K V : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K V,
      ((finrank K W : ℝ)/finrank K V)*finrank K L+
        D*(min (finrank K L) (finrank K V-finrank K L) : ℕ) ≤
        finrank K (Quartic.BilinearImage.image mu L)) :
    ∃ Q : Fin q → F, finrank K (multiplication mu Q).range =
      min (q*finrank K V) (finrank K W) := by
  let R : ℝ := (finrank K W : ℝ)/finrank K V
  have hAr : (0 : ℝ) < finrank K V := by exact_mod_cast hA
  by_cases hq : q*finrank K V ≤ finrank K W
  · have hqR : (q : ℝ) ≤ R := by
      apply (le_div_iff₀ hAr).mpr
      exact_mod_cast hq
    obtain ⟨P,⟨Q,hQ⟩,hP⟩ := generic_injective_of_strict_shadow (q := q) mu R D hqR hD hgrowth
    refine ⟨Q,?_⟩
    rw [LinearMap.finrank_range_of_inj (hP Q hQ),Module.finrank_pi_fintype,min_eq_left hq]
    simp
  · have hqR : R ≤ q := by
      apply (div_le_iff₀ hAr).mpr
      exact_mod_cast (show finrank K W ≤ q*finrank K V by omega)
    have hT : (finrank K W : ℝ)=R*finrank K V := by dsimp [R]; field_simp
    obtain ⟨P,⟨Q,hQ⟩,hP⟩ := generic_surjective_actual_of_strict_shadow (q := q) mu R D hT hqR hD hgrowth
    refine ⟨Q,?_⟩
    rw [LinearMap.range_eq_top.mpr (hP Q hQ),finrank_top,min_eq_right (by omega)]

end Froberg.BilinearScalarFamily
