import Froberg.PreparedWitnessEmbedding
import Froberg.FiniteFourthRow
import Froberg.PreparedFiniteRows
import Froberg.BiformKernelIntersection

/-! Finite capacity hypotheses produce actual row witnesses inside one common
prepared parameter space. No row-specific coefficient variables remain. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

/-- The explicit finite bounds used by the generic higher even-row witness. -/
structure FourthRowCapacity (w v d q b : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) : Prop where
  hw : 0<w
  hv : 0<v
  low : ∀ j∈J,2≤j
  even : ∀ j∈J,Even j
  degree : ∀ j∈J,j≤d
  new_unconstrained : T 4=0
  diagonal : counts 2≤(w.choose 2-finrank K X)*(v.choose (d-2)/2)
  output_positive : 0<oddOutputDimension w 4
  enough_generators : counts 4≤b*(v+v+(d-4)-1).choose (d-4)
  divisor_capacity : b*((d-4)+d).choose (d-4)≤oddOutputDimension w 4
  incidence : oddOutputDimension w 4*((d-4)+d).choose (d-4) *
    (Fintype.card (Label q J counts)+oddOutputDimension w 4*(v+v+(d-4)-1).choose (d-4)+
      (oddOutputDimension w 4*2^(oddOutputDimension w 4))*(v+v+(d-1)-1).choose (d-1)) ≤
    (oddOutputDimension w 4-b*((d-4)+d).choose (d-4))*(v+v+(d-4)+d-1).choose d
  scalar_open : ∃ D : MvPolynomial
      (Fin (finrank K (Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d))) K,
    (∃ Q : Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d,
      eval (coordinates K _ Q) D≠0) ∧
    ∀ Q : Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d,
      eval (coordinates K _ Q) D≠0 →
      Function.Injective (ProjectedPrefix.multiplication
        (fun α => MonomialExpansion.partialDegree (balancedScalarHalf v) α≠2*((d-2)/2)) Q (d-4))

/-- The complete finite construction lands in the prescribed common family. -/
theorem exists_fourth_row_parameter {w v d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X} (h4 : 4∈J)
    (h : FourthRowCapacity w v d q b J counts T) :
    ∃ p : Space (v+v) d q J counts (constrainedOutputs T),
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) ⟨4,h4⟩ i p) ∧
      (row (fun _ _ => inf_le_left) ⟨4,h4⟩ p).ker=
        (rowConstants (fun _ _ => inf_le_left) ⟨4,h4⟩ p).range := by
  obtain ⟨o,e,z,he,Q,E,ho,hdeg,hER,hRdeg,hrest,hzero,hker⟩ :=
    exists_finite_fourth_row h.hw h.hv counts J (fun j hj => by have := h.low j hj; omega) h.even h.degree T
      h.low h.diagonal h.output_positive h.enough_generators h.divisor_capacity h.incidence h.scalar_open
  have hmem : ∀ j∈J,∀ i,E j i∈biformImage (constrainedOutputs T j) (Forms K (v+v) (d-j)) := by
    intro j hj i
    by_cases hjR : j=4
    · subst j
      rw [hER i,constrainedOutputs,h.new_unconstrained,LinearMap.ker_zero,inf_top_eq]
      rw [← polynomialFormVector_attachedCoordinates o e z he i]
      exact polynomialFormVector_mem_biform o _ _ hdeg _ (fun a => (attachedCoordinates e z he i a).property)
    · apply mem_biformImage_inf_kernel
      · apply mem_biformImage_of_homogeneous
        · simpa only [Nat.add_sub_of_le (h.degree j hj)] using (hrest j hjR i).1
        · exact (hrest j hjR i).2.1
      · exact (hrest j hjR i).2.2
  exact sparse_witness_common_parameter (fun _ _ => inf_le_left) ⟨4,h4⟩ o ho hdeg e z he Q E hmem hER (hzero 0 (Nat.zero_le d)) hker

end Froberg.PreparedParameters
