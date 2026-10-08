import Froberg.ProjectedQuotientMultiplication
import Froberg.ClosedCoefficientStrata

/-! Maximal rank of the actual projected first normal map. A coefficient
projection is allowed, so the odd coefficient space in C.6 is represented
without introducing spurious even contraction kernels. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Quartic PolynomialBilinearCoordinates
open BilinearCovectorCharts BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {Z : Type*} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
variable {n d r t a b T : ℕ}

/-- Actual homology coefficients followed by a specified coefficient projection. -/
def projectedMappedCoefficients (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K)) :
    ProjectedEndpointHomology pi q →ₗ[K] (Fin t → Fin a → K) :=
  (vmap.compLeft (Fin t)).comp
    (projectedHomologyCoefficients htwo pi q hq (Submodule.span K (Set.range q)) dual)

abbrev ProjectedCoefficientQuotient (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K)) :=
  ProjectedEndpointHomology pi q ⧸ (projectedMappedCoefficients htwo pi q hq dual vmap).ker

/-- The faithful map from its genuine coefficient-kernel quotient. -/
def faithfulProjectedCoefficients (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K)) :
    ProjectedCoefficientQuotient htwo pi q hq dual vmap →ₗ[K] (Fin t → Fin a → K) :=
  let c := projectedMappedCoefficients htwo pi q hq dual vmap
  c.ker.liftQ c le_rfl

theorem faithfulProjectedCoefficients_injective (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K)) :
    Function.Injective (faithfulProjectedCoefficients htwo pi q hq dual vmap) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- Literal product compatibility implies the exact coordinate factorization
of the projected normal map through its faithful coefficients. -/
theorem projectedNormalMap_coordinate_factorization (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K))
    (eJ : ProjectedEndpointCokernel pi q ≃ₗ[K] (Fin T → K))
    (phi : (Fin b → K) →ₗ[K] Forms K n d)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ z v, mu z (vmap v) = eJ (projectedQuotientProduct pi q (phi z) v))
    (z : Fin t → Fin b → K) :
    eJ.toLinearMap.comp (projectedNormalMap pi q (relativeGeneratorMotion q dual (fun i => phi (z i)))) =
      (CoefficientMotion.motion mu (faithfulProjectedCoefficients htwo pi q hq dual vmap) z).comp
        (projectedMappedCoefficients htwo pi q hq dual vmap).ker.mkQ := by
  rw [projectedNormalMap_canonical_coefficient_formula htwo pi q hq dual]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply,CoefficientMotion.motion_apply,coefficientResponse_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (hmu (z i)
    (projectedHomologyCoefficients htwo pi q hq (Submodule.span K (Set.range q)) dual x i)).symm

/-- Source quotienting and target coordinates preserve the exact response rank. -/
theorem projectedNormalMap_rank_eq_coefficient_motion (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K))
    (eJ : ProjectedEndpointCokernel pi q ≃ₗ[K] (Fin T → K))
    (phi : (Fin b → K) →ₗ[K] Forms K n d)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ z v, mu z (vmap v) = eJ (projectedQuotientProduct pi q (phi z) v))
    (z : Fin t → Fin b → K) :
    finrank K (projectedNormalMap pi q (relativeGeneratorMotion q dual (fun i => phi (z i)))).range =
      finrank K (CoefficientMotion.motion mu (faithfulProjectedCoefficients htwo pi q hq dual vmap) z).range := by
  have hf := projectedNormalMap_coordinate_factorization htwo pi q hq dual vmap eJ phi mu hmu z
  have hr := congrArg (fun F => finrank K (LinearMap.range F)) hf
  rw [LinearMap.range_comp,eJ.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ _)] at hr
  exact hr

/-- C.6 on the actual projected complex, with literal scalar-incidence budget. -/
theorem exists_maximal_projected_normal (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K))
    (eJ : ProjectedEndpointCokernel pi q ≃ₗ[K] (Fin T → K))
    (phi : (Fin b → K) →ₗ[K] Forms K n d)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ z v, mu z (vmap v) = eJ (projectedQuotientProduct pi q (phi z) v))
    (hbudget : ∀ ell : Fin T → K, ell ≠ 0 →
      let k := finrank K (LinearMap.ker (relationMap mu ell))
      let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
      (k*(a-k) : ℕ)+(T : ℤ)-e-1 <
        (CoefficientMotion.coefficientSliceCount
          (finrank K (ProjectedCoefficientQuotient htwo pi q hq dual vmap)) t T k : ℕ)) :
    ∃ z : Fin t → Fin b → K,
      finrank K (projectedNormalMap pi q (relativeGeneratorMotion q dual (fun i => phi (z i)))).range =
        min (finrank K (ProjectedCoefficientQuotient htwo pi q hq dual vmap)) T := by
  obtain ⟨z,hz⟩ := CoefficientMotion.exists_maximal_motion_of_incidence_budget mu
    (faithfulProjectedCoefficients htwo pi q hq dual vmap)
    (faithfulProjectedCoefficients_injective htwo pi q hq dual vmap) hbudget
  refine ⟨z,?_⟩
  rw [projectedNormalMap_rank_eq_coefficient_motion htwo pi q hq dual vmap eJ phi mu hmu z]
  exact hz

/-- The C.4 closed-stratum interface for the actual projected normal map.
This version consumes genuine empty projective sections and does not replace
the multilayer C.4 estimate by a stronger global Grassmannian shadow. -/
theorem exists_maximal_projected_normal_of_slices (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K))
    (eJ : ProjectedEndpointCokernel pi q ≃ₗ[K] (Fin T → K))
    (phi : (Fin b → K) →ₗ[K] Forms K n d)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ z v, mu z (vmap v) = eJ (projectedQuotientProduct pi q (phi z) v))
    (count slices : Fin (a+1) → ℕ)
    (degrees : ∀ k, Fin (count k) → ℕ)
    (eqs : ∀ k, (i : Fin (count k)) → Forms K T (degrees k i))
    (cuts : ∀ k, Fin (slices k) → Forms K T 1)
    (hempty : ∀ k (ell : Fin T → K),
      (∀ i, MvPolynomial.aeval ell (eqs k i).val = 0) →
      (∀ j, MvPolynomial.aeval ell (cuts k j).val = 0) → ell = 0)
    (hcover : ∀ (ell : Fin T → K) (k : Fin (a+1)),
      finrank K (LinearMap.ker (relationMap mu ell)) = k.val →
      ∀ i, MvPolynomial.eval ell (eqs k i).val = 0)
    (hcount : ∀ k, slices k ≤
      (finrank K (ProjectedCoefficientQuotient htwo pi q hq dual vmap)-t*k.val)+
        (T-finrank K (ProjectedCoefficientQuotient htwo pi q hq dual vmap))) :
    ∃ z : Fin t → Fin b → K,
      finrank K (projectedNormalMap pi q (relativeGeneratorMotion q dual (fun i => phi (z i)))).range =
        min (finrank K (ProjectedCoefficientQuotient htwo pi q hq dual vmap)) T := by
  obtain ⟨z,hz⟩ := CoefficientMotion.exists_maximal_motion mu
    (faithfulProjectedCoefficients htwo pi q hq dual vmap)
    (faithfulProjectedCoefficients_injective htwo pi q hq dual vmap)
    count slices degrees eqs cuts hempty hcover hcount
  refine ⟨z,?_⟩
  rw [projectedNormalMap_rank_eq_coefficient_motion htwo pi q hq dual vmap eJ phi mu hmu z]
  exact hz

end Froberg
