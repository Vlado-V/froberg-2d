module

public import Quartic.SlicedCovectorAvoidance
public import Quartic.IteratedCovectorCharts

@[expose] public section

/-!
# Actual prefix-profile covector strata with auxiliary linear slices

The original iterated polynomial charts and their literal Cell bound feed the
joint shared-coefficient/slice exclusion theorem. The result is an empty
sliced stratum, with every profile interpreted through the actual coordinate
flag. It does not assert unsliced generic fiber dimensions.
-/
noncomputable section
namespace Quartic.IteratedSlicedCovectorCharts
open Module MvPolynomial IteratedBlockCharts IteratedCovectorCharts
open PolynomialBilinearCoordinates (coordinates)
open BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K] [Infinite K] {n B T e q s : ℕ}
variable {b r : Fin n → ℕ}

/-- A genuine prefix profile is empty after adjoining s actual homogeneous
linear slices when its joint projective parameter budget is negative. -/
theorem principal_open_excludes_profile_of_int_bound
    (mu : (Fin B → K) →ₗ[K] (Fin (∑ i,b i) → K) →ₗ[K] (Fin T → K))
    (g : ℤ) (hg : (parameterCount b r:ℤ) ≤ g)
    (hcount : g+(T:ℤ)-(e:ℤ)-1 < (q*((∑ i,b i)-(∑ i,r i))+s:ℕ)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K B T q s))) K,
      (∃ x : SharedCovectorPolynomial.Input K B T q s,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K B T q s,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,ell ≠ 0 →
        (∀ i,finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
          ((LinearMap.ker (relationMap mu ell)).comap (IteratedCovectorCharts.coordinates K b).toLinearMap) i)=r i) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ¬((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
  classical
  obtain ⟨P,hP,hgood⟩ := SlicedCovectorAvoidance.principal_open_excludes_sliced_stratum_of_int_bound
    (d := ∑ i,r i) (e := e) (q := q) (s := s) mu (fun j : Selectors b r => graphPolynomial j) g
    (by intro j; rw [IteratedBlockCharts.parameter_count]; exact hg) hcount
  refine ⟨P,hP,?_⟩
  intro x hx ell hell hprofile himage
  exact hgood x hx ell hell (finrank_of_profile _ hprofile) (covered_of_profile _ hprofile) himage

open ProfileChartBound ProfileCertificate LayerRankCounts

/-- The manuscript Cell bound applies to the same actual ordered kernel
profile, while the auxiliary target columns supply s further equations. -/
theorem principal_open_excludes_Cell_profile
    (m c i : ℕ) (hi : i ≤ coreA c) (r : Fin (freeW m c) → ℕ) (hr : ∀ k,r k ≤ 3)
    (mu : (Fin B → K) →ₗ[K]
      (Fin (∑ k,blockDimensions (coreA c) (freeW m c) k) → K) →ₗ[K] (Fin T → K))
    (hcount : Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3)+
      (T:ℤ)-(e:ℤ)-1 < (q*(totalA m c-profileDim i (levelCount r 1) (levelCount r 2) (levelCount r 3))+s:ℕ)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K B T q s))) K,
      (∃ x : SharedCovectorPolynomial.Input K B T q s,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K B T q s,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,ell ≠ 0 →
        (∀ k,finrank K (FilteredImage.initialPiece
          (fun k => Fin (blockDimensions (coreA c) (freeW m c) k) → K)
          ((LinearMap.ker (relationMap mu ell)).comap
            (IteratedCovectorCharts.coordinates K (blockDimensions (coreA c) (freeW m c))).toLinearMap) k)=blockRanks i r k) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ¬((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
  apply principal_open_excludes_profile_of_int_bound mu
    (Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3))
    (parameterCount_le_Cell m c i hi r hr)
  simpa only [sum_blockDimensions,sum_blockRanks i r hr] using hcount

end Quartic.IteratedSlicedCovectorCharts
