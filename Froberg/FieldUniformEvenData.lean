module

public import Froberg.FieldUniformEvenCapacities
public import Froberg.ShiftedFiniteEvenReduction
public import Froberg.ExtendedLeadingWitnesses
public import Froberg.NaturalEventualParity

@[expose] public section

/-! The scalar/even background with the actual counts has the literal
positive-row reduction on a nonempty open. This is the U=0 input to even
degree restoration, with any fixed appended quadratic slots included. -/
noncomputable section
universe u
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
theorem eventually_field_uniform_even_all_scalar_data {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
        let S := Space n d (upperCount n d) (allEvenIndices d)
          (allEvenCount d (2*w) n (e n+extra)) (constrainedOutputs T)
        (∀ R : allEvenIndices d,∃ p : S,LinearIndependent K (p.2 R)) ∧
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_field_uniform_actual_even_capacities_shift hd] with w hw
  intro extra e he
  have hs (z : ℕ) := hw z extra e he
  have hext (z : ℕ) :
      ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
        let S := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        (∀ R : allEvenIndices d,∃ p : S,LinearIndependent K (p.2 R)) ∧
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 → EvenPositiveReduction p := by
    filter_upwards [hs z,eventually_gt_atTop 0] with v hv hvpos
    intro K _ _ X _ _ _ T hX hO hT
    obtain ⟨hq,hh,hp⟩ := hv K X T hX hO hT
    let counts := allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)
    let I := Label (upperCount (v+v+z) d) (allEvenIndices d) counts
    letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
    have hJ : ∀ j∈allEvenIndices d,2≤j := fun _ hj => (mem_allEvenIndices.mp hj).1
    have hdegree : ∀ j∈allEvenIndices d,j≤d := fun _ hj => (mem_allEvenIndices.mp hj).2.1
    have heven : ∀ j∈allEvenIndices d,j%2=0 := fun _ hj => (mem_allEvenIndices.mp hj).2.2
    have h2 : 2∈allEvenIndices d := mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩
    have hcover : ∀ r,0<r → r≤d → r%2=0 → r∈allEvenIndices d := by
      intro r hr hrd hre
      exact mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩
    exact ⟨all_even_extended_leading (by omega) hvpos T hJ hdegree h2 ⟨_,hq⟩
      (fun R hR => ⟨_,hh R hR⟩),
      finite_even_reduction_open_shift (by omega) hvpos T hJ hdegree heven h2 hcover
        ⟨_,hq⟩ (fun R hR => ⟨_,hh R hR⟩) (fun R _ _ _ => hp R)⟩
  exact eventually_of_twice_add_shifts 0 _ (hext 0) (hext 1)

end Froberg.PreparedParameters
