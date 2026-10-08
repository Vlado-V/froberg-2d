import Froberg.ProjectionCharts

/-! Actual projections avoid rank failure on a polynomial family of image
spaces when the Schubert equation count exceeds the parameter count. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.SubspaceCharts Quartic.BilinearCovectorCharts
variable {K I U V : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {b t w : ℕ}

/-- One rank stratum of a polynomial family is avoided on a nonempty
principal open of actual projection maps. -/
theorem projection_family_rank_open
    (A : (I → K) → (U →ₗ[K] V)) (hA : IsPolynomialFamily A)
    (hcount : Fintype.card I + t*(b-t) < w*(b-t)) :
    ∃ D : MvPolynomial (Fin (finrank K (V →ₗ[K] (Fin b → K)))) K,
      (∃ x, eval x D ≠ 0) ∧
      ∀ x, eval x D ≠ 0 → ∀ p,
        w ≤ finrank K (A p).range →
        finrank K (((Module.finBasis K (V →ₗ[K] (Fin b → K))).equivFun.symm x).comp (A p)).range ≠ t := by
  classical
  let J := Fin t ↪ Fin b
  let B := Module.finBasis K (V →ₗ[K] (Fin b → K))
  have hlocal (j : J) :
      ∃ D : MvPolynomial (Fin (finrank K (V →ₗ[K] (Fin b → K)))) K,
        (∃ x, eval x D ≠ 0) ∧
        ∀ x, eval x D ≠ 0 → ∀ p : I → K, ∀ q : GraphParameters j → K,
          w ≤ finrank K (A p).range →
          (graphQuotient j q).comp ((B.equivFun.symm x).comp (A p)) ≠ 0 := by
    let AA (z : Sum I (GraphParameters j) → K) := A (z ∘ Sum.inl)
    let CC (z : Sum I (GraphParameters j) → K) := graphQuotient j (z ∘ Sum.inr)
    have hpoly := polynomial_sandwich_family AA CC
      (polynomial_family_reindex hA Sum.inl)
      (polynomial_family_reindex (graphQuotient_polynomial j) Sum.inr)
    have hn : Fintype.card (Sum I (GraphParameters j)) < w*(b-t) := by
      simpa only [Fintype.card_sum,card_coefficient_positions] using hcount
    obtain ⟨D,hD,havoid⟩ := polynomial_linear_kernel_avoidance
      (fun z => sandwichMap (AA z) (CC z)) hpoly hn
    refine ⟨D,hD,?_⟩
    intro x hx p q hp
    have hr : w*(b-t) ≤ finrank K (sandwichMap (AA (Sum.elim p q)) (CC (Sum.elim p q))).range := by
      rw [sandwichMap_rank]
      change w*(b-t) ≤ finrank K (A p).range * finrank K (graphQuotient j q).range
      rw [graphQuotient_rank]
      exact Nat.mul_le_mul_right _ hp
    exact havoid x hx (Sum.elim p q) hr
  choose D hD havoid using hlocal
  have hnz (j : J) : D j ≠ 0 := by
    obtain ⟨x,hx⟩ := hD j
    intro hz
    simp [hz] at hx
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ j, D j,⟨x,by simpa using Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)⟩,?_⟩
  intro x hx p hp heq
  obtain ⟨j,q,hq⟩ := exists_chart ((B.equivFun.symm x).comp (A p)).range heq
  have hxj : eval x (D j) ≠ 0 := by
    have hh : ∏ j, eval x (D j) ≠ 0 := by simpa using hx
    exact Finset.prod_ne_zero_iff.mp hh j (Finset.mem_univ _)
  apply havoid j x hxj p (fun z => q z.1 z.2) hp
  apply LinearMap.ext
  intro u
  change ((B.equivFun.symm x).comp (A p)) u ∈ (graphQuotient j (fun z => q z.1 z.2)).ker
  rw [graphQuotient_ker]
  change ((B.equivFun.symm x).comp (A p)) u ∈ chartSubspace j q
  rw [hq]
  exact LinearMap.mem_range_self _ u

end Froberg
