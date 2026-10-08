import Froberg.ProjectedNormalRank
import Froberg.ThinNormalBudget
import Froberg.LocalComparison

/-! The thin C.4 bounds supply the exact slice counts required by the actual
projected normal map and hence the local comparison data. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic PolynomialBilinearCoordinates
open BilinearCovectorCharts BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {Z : Type*} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
variable {n d r t a b T : ℕ}

theorem exists_maximal_projected_normal_of_thin_slices (htwo : (2 : K) ≠ 0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K))
    (eJ : ProjectedEndpointCokernel pi q ≃ₗ[K] (Fin T → K))
    (phi : (Fin b → K) →ₗ[K] Forms K n d)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ z v, mu z (vmap v) = eJ (projectedQuotientProduct pi q (phi z) v))
    (C : ℝ) (hC : (t : ℝ) ≤ C)
    (count : Fin (a+1) → ℕ)
    (degrees : ∀ k, Fin (count k) → ℕ)
    (eqs : ∀ k, (i : Fin (count k)) → Forms K T (degrees k i))
    (cuts : ∀ k, Fin (BilinearCovectorStrata.thinSlices T C k.val) → Forms K T 1)
    (hempty : ∀ k (ell : Fin T → K),
      (∀ i, MvPolynomial.aeval ell (eqs k i).val = 0) →
      (∀ j, MvPolynomial.aeval ell (cuts k j).val = 0) → ell = 0)
    (hcover : ∀ (ell : Fin T → K) (k : Fin (a+1)),
      finrank K (LinearMap.ker (relationMap mu ell)) = k.val →
      ∀ i, MvPolynomial.eval ell (eqs k i).val = 0) :
    ∃ z : Fin t → Fin b → K,
      finrank K (projectedNormalMap pi q (relativeGeneratorMotion q dual (fun i => phi (z i)))).range =
        min (finrank K (ProjectedCoefficientQuotient htwo pi q hq dual vmap)) T := by
  apply exists_maximal_projected_normal_of_slices htwo pi q hq dual vmap eJ phi mu hmu
    count (fun k => BilinearCovectorStrata.thinSlices T C k.val) degrees eqs cuts hempty hcover
  intro k
  exact thinSlices_le_coefficientSliceCount _ t T k.val C hC

theorem exists_local_comparison_of_thin_slices (htwo : (2 : K) ≠ 0)
    (D : Submodule K (Forms K n (2*d))) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] (Fin a → K))
    (eJ : ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] (Fin T → K))
    (phi : (Fin b → K) →ₗ[K] Forms K n d)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ z v, mu z (vmap v) = eJ (projectedQuotientProduct D.mkQ q (phi z) v))
    (C : ℝ) (hC : (t : ℝ) ≤ C)
    (count : Fin (a+1) → ℕ)
    (degrees : ∀ k, Fin (count k) → ℕ)
    (eqs : ∀ k, (i : Fin (count k)) → Forms K T (degrees k i))
    (cuts : ∀ k, Fin (BilinearCovectorStrata.thinSlices T C k.val) → Forms K T 1)
    (hempty : ∀ k (ell : Fin T → K),
      (∀ i, MvPolynomial.aeval ell (eqs k i).val = 0) →
      (∀ j, MvPolynomial.aeval ell (cuts k j).val = 0) → ell = 0)
    (hcover : ∀ (ell : Fin T → K) (k : Fin (a+1)),
      finrank K (LinearMap.ker (relationMap mu ell)) = k.val →
      ∀ i, MvPolynomial.eval ell (eqs k i).val = 0) :
    ∀ B : ℕ,
      finrank K (projectedMappedCoefficients htwo D.mkQ q hq dual vmap).ker ≤ B →
      finrank K D ≤ B → Nonempty (LocalComparisonData K n d r B) := by
  intro B hkernel hdeleted
  obtain ⟨z,hz⟩ := exists_maximal_projected_normal_of_thin_slices htwo D.mkQ q hq
    dual vmap eJ phi mu hmu C hC count degrees eqs cuts hempty hcover
  refine ⟨{
    deleted := D
    generators := q
    independent := hq
    motion := relativeGeneratorMotion q dual (fun i => phi (z i))
    retained := (projectedMappedCoefficients htwo D.mkQ q hq dual vmap).ker
    normal_rank := ?_
    retained_bound := hkernel
    deleted_bound := hdeleted
  }⟩
  have hdim : finrank K (ProjectedEndpointCokernel D.mkQ q)=T := by
    simpa using eJ.finrank_eq
  rw [hdim]
  exact hz

end Froberg
