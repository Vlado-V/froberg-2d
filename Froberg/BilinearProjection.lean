import Froberg.ProjectionRankAvoidance

/-! The projection incidence argument applied to actual bilinear product
images, with every source subspace covered by finite polynomial charts. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic Quartic.SubspaceCharts Quartic.BilinearCovectorCharts
variable {K : Type*} [Field K] [Infinite K] {a B N b ell t w : ℕ}

/-- Graph-chart basis vectors are literal polynomial families. -/
theorem graphVector_coordinate_polynomial (j : Fin ell ↪ Fin a) (i : Fin ell) :
    IsPolynomialFamily (fun p : GraphParameters j → K => graphVector j p i) := by
  classical
  intro L
  refine ⟨∑ k, graphPolynomial j i k * C (L (Pi.single k 1)),?_⟩
  intro p
  change _ = L (graphVector j p i)
  simp only [map_sum,map_mul,eval_graphPolynomial,MvPolynomial.eval_C]
  calc
    _ = L (∑ k, graphVector j p i k • Pi.single k 1) := by
      simp only [map_sum,map_smul,smul_eq_mul]
    _ = L (graphVector j p i) := by
      congr 1
      funext k
      simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

/-- The actual product map on a graph-chart basis varies polynomially. -/
theorem graphTupleMap_polynomial
    (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin N → K))
    (j : Fin ell ↪ Fin a) :
    IsPolynomialFamily (fun p : GraphParameters j → K => BilinearImage.tupleMap mu (graphVector j p)) := by
  apply isPolynomialFamily_linearMap
  intro v
  have h := IsPolynomialFamily.sum (fun i => (graphVector_coordinate_polynomial j i).linear_comp (mu (v i)))
  simpa only [BilinearImage.tupleMap_apply] using h

/-- A nonempty projection open excludes one bad output rank for every
source subspace of a specified dimension and product-rank lower bound. -/
theorem bilinear_projection_rank_open
    (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin N → K))
    (hcount : ell*(a-ell)+t*(b-t) < w*(b-t)) :
    ∃ D : MvPolynomial (Fin (finrank K ((Fin N → K) →ₗ[K] (Fin b → K)))) K,
      (∃ x, eval x D ≠ 0) ∧
      ∀ x, eval x D ≠ 0 → ∀ L : Submodule K (Fin a → K),
        finrank K L = ell → w ≤ finrank K (BilinearImage.image mu L) →
        finrank K ((BilinearImage.image mu L).map
          ((Module.finBasis K ((Fin N → K) →ₗ[K] (Fin b → K))).equivFun.symm x)) ≠ t := by
  classical
  let J := Fin ell ↪ Fin a
  have hlocal (j : J) := projection_family_rank_open
    (fun p : GraphParameters j → K => BilinearImage.tupleMap mu (graphVector j p))
    (graphTupleMap_polynomial mu j)
    (by simpa only [card_coefficient_positions] using hcount)
  choose D hD hgood using hlocal
  have hnz (j : J) : D j ≠ 0 := by
    obtain ⟨x,hx⟩ := hD j
    intro h
    simp [h] at hx
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ j, D j,⟨x,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)
  intro x hx L hL hw
  obtain ⟨j,p,hp⟩ := exists_chart L hL
  let pp : GraphParameters j → K := fun z => p z.1 z.2
  have he : (BilinearImage.tupleMap mu (graphVector j pp)).range = BilinearImage.image mu L := by
    rw [BilinearImage.range_tupleMap,graphVector_span]
    change BilinearImage.image mu (chartSubspace j p) = _
    rw [hp]
  have hxj : eval x (D j) ≠ 0 := by
    have hh : ∏ j, eval x (D j) ≠ 0 := by simpa only [map_prod] using hx
    exact Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ _)
  have h := hgood j x hxj pp (by rwa [he])
  rwa [LinearMap.range_comp,he] at h

end Froberg
