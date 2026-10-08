import Froberg.PreparedActualReduction
import Froberg.UniformShiftedPreparedCapacities

/-! The actual even-reduction open with its output target selected after the
output dimension, so the target module may vary with that dimension. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
variable {K : Type} [Field K] [Infinite K]

theorem eventually_actual_even_reduction_open_uniform {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        let S := Space (v+v) d (upperCount (v+v) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v) (e (v+v)+extra)) (constrainedOutputs T)
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  filter_upwards [eventually_actual_even_capacities_shift_uniform (K := K) hd] with w hw
  intro X _ _ _ T hX hO hT extra e he
  filter_upwards [hw X T hX hO hT 0 extra e he] with v hv
  simp only [Nat.add_zero] at hv
  let counts := allEvenCount d (2*w) (v+v) (e (v+v)+extra)
  let I := Label (upperCount (v+v) d) (allEvenIndices d) counts
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hJ : ∀ j∈allEvenIndices d,2≤j := fun _ hj => (mem_allEvenIndices.mp hj).1
  have hdegree : ∀ j∈allEvenIndices d,j≤d := fun _ hj => (mem_allEvenIndices.mp hj).2.1
  have heven : ∀ j∈allEvenIndices d,j%2=0 := fun _ hj => (mem_allEvenIndices.mp hj).2.2
  have h2 : 2∈allEvenIndices d := mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩
  have hcover : ∀ r,0<r → r≤d → r%2=0 → r∈allEvenIndices d := by
    intro r hr hrd hre
    exact mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩
  exact finite_even_reduction_open T hJ hdegree heven h2 hcover ⟨_,hv.1⟩ (fun R hR => ⟨_,hv.2.1 R hR⟩)
    (fun R _ _ _ => hv.2.2 R)

end Froberg.PreparedParameters
