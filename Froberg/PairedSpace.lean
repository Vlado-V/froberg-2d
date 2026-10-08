import Froberg.PairedAssembly
import Froberg.PairedSurjection
import Froberg.SymmetricProducts

/-! The independent symmetric-product space of Lemma 4.1. -/
noncomputable section
namespace Froberg.PairedMonomials
open Finset ProductFibers Module
variable {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}

/-- x variables have bidegree (1,0), and y variables have bidegree (0,1). -/
def pairedWeight (z : X × Bool) : ℕ × ℕ := if z.2 then (1,0) else (0,1)

theorem weight_pairedExponent {S A : Finset X} (hA : A ⊆ S) :
    Finsupp.weight pairedWeight (pairedExponent S A) = (A.card, S.card-A.card) := by
  have hx : (∑ x, pairedExponent S A (x,true)) = A.card := by
    simp [pairedExponent_true,Finset.inter_eq_right.mpr hA]
  have hy : (∑ x, pairedExponent S A (x,false)) = S.card-A.card := by
    calc
      _ = (S \ A).card := by
        simp [pairedExponent_false]
        congr 1
        ext x
        simp
      _ = _ := Finset.card_sdiff_of_subset hA
  rw [Finsupp.weight_eq_sum,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,pairedWeight,Bool.false_eq_true,reduceIte,
    Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,Prod.mk_add_mk,add_zero,zero_add]
  rw [← prod_mk_sum,hx,hy]

/-- Every specialized form lies in the prescribed homogeneous component. -/
theorem specializedForm_homogeneous {K : Type*} [CommRing K]
    (values : SizedSubset X s × ((X × Bool) →₀ ℕ) → K) (S : SizedSubset X s) :
    specializedForm values S ∈ MvPolynomial.homogeneousSubmodule (X × Bool) K s := by
  classical
  unfold specializedForm ProductMinors.genericForm
  simp only [map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.eval_X,
    MvPolynomial.map_monomial,map_one,MvPolynomial.C_mul_monomial,mul_one]
  apply Submodule.sum_mem
  intro m hm
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hm
  exact MvPolynomial.isHomogeneous_monomial _ ((degree_pairedExponent S.1 A).trans S.2)

/-- Every specialized form has x-degree floor(s/2) and complementary y-degree. -/
theorem specializedForm_bihomogeneous {K : Type*} [CommRing K]
    (values : SizedSubset X s × ((X × Bool) →₀ ℕ) → K) (S : SizedSubset X s) :
    specializedForm values S ∈ MvPolynomial.weightedHomogeneousSubmodule K pairedWeight
      (s/2,s-s/2) := by
  classical
  unfold specializedForm ProductMinors.genericForm
  simp only [map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.eval_X,
    MvPolynomial.map_monomial,map_one,MvPolynomial.C_mul_monomial,mul_one]
  apply Submodule.sum_mem
  intro m hm
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hAS,hAc⟩ := Finset.mem_powersetCard.mp hA
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _
    (by rw [weight_pairedExponent hAS,hAc,S.2])

/-- All unordered products of one common specialized family are independent. -/
theorem exists_independent_pairProducts {K : Type} [Field K] [Infinite K] :
    ∃ values : SizedSubset X s × ((X × Bool) →₀ ℕ) → K,
      LinearIndependent K (pairProducts (specializedForm values)) := by
  classical
  obtain ⟨values,h⟩ := exists_independent_fiber_products (X := X) (s := s) (K := K)
  refine ⟨values,?_⟩
  have hc : LinearIndependent K
      (pairProducts (specializedForm values) ∘ allColumns (X := X) (s := s)) := h
  choose f hf using (allColumns_surjective (X := X) (s := s))
  have hfi : Function.Injective f := by
    intro i j hij
    rw [← hf i,← hf j,hij]
  have hi := hc.comp f hfi
  simpa only [Function.comp_def,hf] using hi

theorem card_sizedSubset (s : ℕ) : Fintype.card (SizedSubset X s) = (Fintype.card X).choose s := by
  have h : (Finset.univ.filter (fun S : Finset X => S.card=s)) =
      (Finset.univ : Finset X).powersetCard s := by
    ext S
    simp
  rw [Fintype.card_subtype,h,Finset.card_powersetCard,Finset.card_univ]

/-- Lemma 4.1: an actual bihomogeneous subspace of the asserted dimension with
injective multiplication on mathlib's symmetric-square quotient. The construction
also covers s=0 and s>|X|. -/
theorem exists_space_independent_symmetric_products {K : Type} [Field K] [Infinite K] (s : ℕ) :
    ∃ W : Submodule K (MvPolynomial (X × Bool) K),
      W ≤ MvPolynomial.homogeneousSubmodule (X × Bool) K s ∧
      W ≤ MvPolynomial.weightedHomogeneousSubmodule K pairedWeight (s/2,s-s/2) ∧
      finrank K W = (Fintype.card X).choose s ∧
      Function.Injective (subspaceSymmetricMultiplication W) := by
  obtain ⟨values,hprod⟩ := exists_independent_pairProducts (X := X) (s := s) (K := K)
  let q := specializedForm values
  refine ⟨Submodule.span K (Set.range q),?_,?_,?_,?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨S,rfl⟩; exact specializedForm_homogeneous values S)
  · exact Submodule.span_le.mpr (by rintro _ ⟨S,rfl⟩; exact specializedForm_bihomogeneous values S)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hprod),card_sizedSubset]
  · exact symmetricMultiplication_injective_of_pairProducts q hprod

/-- The paired variables formulation of Lemma 4.1 with the conventional variable count. -/
theorem paired_space_exists {K : Type} [Field K] [Infinite K] (w s : ℕ) :
    ∃ W : Submodule K (MvPolynomial (Fin w × Bool) K),
      W ≤ MvPolynomial.homogeneousSubmodule (Fin w × Bool) K s ∧
      W ≤ MvPolynomial.weightedHomogeneousSubmodule K pairedWeight (s/2,s-s/2) ∧
      finrank K W = w.choose s ∧
      Function.Injective (subspaceSymmetricMultiplication W) := by
  simpa only [Fintype.card_fin] using exists_space_independent_symmetric_products (X := Fin w) (K := K) s

end Froberg.PairedMonomials
