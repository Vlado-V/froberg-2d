import Froberg.PolynomialLinearAvoidance
import Froberg.SandwichRank
import Quartic.BilinearCovectorCharts

/-! The literal quotient maps for Grassmannian graph charts and the exact
number of equations imposed on a varying projection. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module Quartic Quartic.SubspaceCharts Quartic.BilinearCovectorCharts
variable {K : Type*} [Field K] {b t : ℕ}

/-- A graph chart is cut out by its outside coordinates minus its graph. -/
def graphQuotient (j : Fin t ↪ Fin b) (p : GraphParameters j → K) :
    (Fin b → K) →ₗ[K] (Outside j → K) :=
  outsideProjection j - (parameterMap (graphCoefficients j p)).comp (selectedProjection j)

@[simp] theorem graphQuotient_ker (j : Fin t ↪ Fin b) (p : GraphParameters j → K) :
    (graphQuotient j p).ker = chartSubspace j (graphCoefficients j p) := rfl

theorem graphQuotient_rank (j : Fin t ↪ Fin b) (p : GraphParameters j → K) :
    finrank K (graphQuotient j p).range = b-t := by
  have hr := LinearMap.finrank_range_add_finrank_ker (graphQuotient j p)
  rw [graphQuotient_ker,chartSubspace_finrank,Module.finrank_pi_fintype,
    finrank_self,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hr
  omega

/-- Polynomiality remains literal after selecting parameter coordinates. -/
theorem polynomial_family_reindex {I J V : Type*} [AddCommGroup V] [Module K V]
    {f : (I → K) → V} (hf : IsPolynomialFamily f) (u : I → J) :
    IsPolynomialFamily (fun p : J → K => f (p ∘ u)) := by
  intro ell
  obtain ⟨P,hP⟩ := hf ell
  exact ⟨MvPolynomial.rename u P,fun p => by simpa only [MvPolynomial.eval_rename] using hP (p ∘ u)⟩

/-- The graph quotient depends polynomially (in fact affinely) on its entries. -/
theorem graphQuotient_polynomial (j : Fin t ↪ Fin b) :
    IsPolynomialFamily (graphQuotient (K := K) j) := by
  classical
  apply isPolynomialFamily_linearMap
  intro x ell
  refine ⟨∑ k, MvPolynomial.C (ell (Pi.single k 1)) *
    (MvPolynomial.C (x k.val) - ∑ i, MvPolynomial.X (k,i) * MvPolynomial.C (x (j i))),?_⟩
  intro p
  change _ = ell (graphQuotient j p x)
  have hc (k : Outside j) : graphQuotient j p x k =
      x k.val-∑ i, p (k,i)*x (j i) := by
    simp only [graphQuotient,LinearMap.sub_apply,Pi.sub_apply,LinearMap.comp_apply,
      parameterMap_apply,graphCoefficients,selectedProjection,outsideProjection,
      LinearMap.pi_apply,LinearMap.proj_apply]
  have hs : (∑ k, (graphQuotient j p x k) • Pi.single k 1)=graphQuotient j p x := by
    funext k
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  calc
    _ = ∑ k, (x k.val-∑ i, p (k,i)*x (j i))*ell (Pi.single k 1) := by
      simp only [map_sum,map_mul,MvPolynomial.eval_C,map_sub,MvPolynomial.eval_X]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = ell (∑ k, (graphQuotient j p x k) • Pi.single k 1) := by
      simp only [map_sum,map_smul,smul_eq_mul,hc]
    _ = ell (graphQuotient j p x) := congrArg ell hs

/-- The equations imposed by a graph quotient on a varying projection have
exactly the expected rank, without any generic-rank assumption. -/
theorem projection_graph_equation_rank {U V : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : U →ₗ[K] V)
    (j : Fin t ↪ Fin b) (p : GraphParameters j → K) :
    finrank K (sandwichMap A (graphQuotient j p)).range =
      finrank K A.range * (b-t) := by
  rw [sandwichMap_rank,graphQuotient_rank]

/-- Polynomiality of the actual sandwich equations. -/
theorem polynomial_sandwich_family {I U V W Z : Type*}
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    (A : (I → K) → (U →ₗ[K] V)) (C : (I → K) → (W →ₗ[K] Z))
    (hA : IsPolynomialFamily A) (hC : IsPolynomialFamily C) :
    IsPolynomialFamily (fun p => sandwichMap (A p) (C p)) := by
  apply isPolynomialFamily_linearMap
  intro P
  exact hC.bilinear (hA.linear_comp (LinearMap.llcomp K U V W P))
    (LinearMap.llcomp K U W Z)

end Froberg
