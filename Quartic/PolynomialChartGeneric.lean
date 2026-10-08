import Quartic.PolynomialSubspaceTupleCharts
import Quartic.PolynomialBilinearCoordinates

/-!
# Generic bilinear injectivity from finite polynomial subspace charts

Each chart may have its own number of parameters and spanning vectors. For
each actual nonzero relation tuple, its chosen chart and actual equation rank
must satisfy g+qd≤rank. Projective normalization saves one parameter, so the
polynomial kernel avoidance theorem then gives a nonempty principal open.
-/

noncomputable section
namespace Quartic.PolynomialChartGeneric
open Module Matrix MvPolynomial KernelPolynomialCharts PolynomialSubspaceTupleCharts
open PolynomialSubspaceCovectorCharts (subspace)
variable {K C : Type*} [Field K] [Fintype C]
variable {I : C → Type*} [∀ c,Fintype (I c)] {N : C → ℕ} {a q n b : ℕ}

/-- A finite polynomial cover with the actual incidence rank bound gives
generic injectivity, even when displayed chart spans vary in dimension. -/
theorem generic_injective [Infinite K]
    (B : (Fin q → Fin a → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    (H : ∀ c,Fin (N c) → Fin a → MvPolynomial (I c) K)
    (hcover : ∀ F : Fin q → Fin a → K,F ≠ 0 →
      ∃ c,∃ t : I c → K,(∀ i,F i ∈ subspace (H c) t) ∧
        Fintype.card (I c)+q*N c ≤ finrank K (LinearMap.range (B F))) :
    ∃ P : MvPolynomial (Fin n) K,(∃ x : Fin n → K,eval x P ≠ 0) ∧
      ∀ x,eval x P ≠ 0 → Function.Injective (B.flip x) := by
  classical
  let Choices := (c : C) × Pivot q (N c)
  have hchart (c : Choices) :
      ∃ P : MvPolynomial (Fin n) K,(∃ x : Fin n → K,eval x P ≠ 0) ∧
        ∀ x,eval x P ≠ 0 → ∀ p : ParameterIndex (I c.1) c.2 → K,
          Fintype.card (I c.1)+q*N c.1 ≤ finrank K (LinearMap.range (B (tupleMap (H c.1) c.2 p))) →
          B (tupleMap (H c.1) c.2 p) x ≠ 0 := by
    have hpos : 0 < q*N c.1 := Nat.mul_pos (Fin.pos c.2.1) (Fin.pos c.2.2)
    have hparam : Fintype.card (ParameterIndex (I c.1) c.2) < Fintype.card (I c.1)+q*N c.1 := by
      rw [PolynomialSubspaceTupleCharts.parameter_count]
      omega
    obtain ⟨P,hP,hgood⟩ := PolynomialKernelAvoidance.principal_open_avoids_kernels
      (equationMatrix B (H c.1) c.2) hparam
    refine ⟨P,hP,?_⟩
    intro x hx p hrank
    have h := hgood x hx p (by rwa [equationMatrix_rank])
    rwa [equationMatrix_mulVec] at h
  choose P hP hgood using hchart
  have hne (c : Choices) : P c ≠ 0 := by
    obtain ⟨x,hx⟩ := hP c
    intro hz
    simp [hz] at hx
  obtain ⟨x₀,hx₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ c,P c,⟨x₀,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun c _ => hx₀ c)
  intro x hx
  have hxP : ∀ c : Choices,eval x (P c) ≠ 0 := by
    simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hx
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  by_contra hnz
  obtain ⟨c,t,hmem,hrank⟩ := hcover F hnz
  obtain ⟨z,p,s,hs,_,hscale⟩ := cover_tuple (H c) t F hnz hmem
  have hrank' : Fintype.card (I c)+q*N c ≤ finrank K (LinearMap.range (B (tupleMap (H c) z p))) := by
    rw [hscale,map_smul,LinearMap.range_smul _ s hs] at hrank
    exact hrank
  apply hgood ⟨c,z⟩ x (hxP ⟨c,z⟩) p hrank'
  change B F x=0 at hF
  rw [hscale,map_smul,LinearMap.smul_apply] at hF
  exact (smul_eq_zero.mp hF).resolve_left hs

section ActualValueSpaces
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
open PolynomialBilinearCoordinates

/-- The coefficient and target spaces may be actual finite-dimensional
polynomial or quotient spaces; only relation vectors use the chart coordinates. -/
theorem generic_injective_actual [Infinite K]
    (B : (Fin q → Fin a → K) →ₗ[K] V →ₗ[K] W)
    (H : ∀ c,Fin (N c) → Fin a → MvPolynomial (I c) K)
    (hcover : ∀ F : Fin q → Fin a → K,F ≠ 0 →
      ∃ c,∃ t : I c → K,(∀ i,F i ∈ subspace (H c) t) ∧
        Fintype.card (I c)+q*N c ≤ finrank K (LinearMap.range (B F))) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ x : V,eval (coordinates K V x) P ≠ 0) ∧
      ∀ x : V,eval (coordinates K V x) P ≠ 0 → Function.Injective (B.flip x) := by
  obtain ⟨P,⟨x,hx⟩,hgood⟩ := generic_injective (coordinate B) H (by
    intro F hF
    obtain ⟨c,t,hmem,hrank⟩ := hcover F hF
    exact ⟨c,t,hmem,by rwa [finrank_range_coordinate]⟩)
  refine ⟨P,⟨(coordinates K V).symm x,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hx
  · intro v hv
    exact (injective_flip_coordinate_at B v).mp (hgood (coordinates K V v) hv)

end ActualValueSpaces
end Quartic.PolynomialChartGeneric
