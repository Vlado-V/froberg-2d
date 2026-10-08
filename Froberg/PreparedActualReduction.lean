import Froberg.PreparedActualCapacities
import Froberg.PreparedFiniteEvenReduction

/-! The scalar/even background with the actual counts has the literal
positive-row reduction on a nonempty open. This is the U=0 input to even
degree restoration, with any fixed appended quadratic slots included. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
variable {σ : Type*} [Fintype σ] {n d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def EvenPositiveReduction (p : Space n d q J counts O) : Prop :=
  ∀ c : Label q J counts → MvPolynomial (σ ⊕ Fin n) K,
    (∀ i,(c i).IsHomogeneous d) →
    (∀ i α,(c i).coeff α≠0 →
      Finsupp.weight (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) α%2=0) →
    (∀ r,0<r → r≤2*d → weightedHomogeneousComponent
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) r (∑ i,generator p i*c i)=0) →
    ∃ (M : Label q J counts → Label q J counts → K)
      (z : Label q J counts → MvPolynomial (σ ⊕ Fin n) K),
      c-matrixBoundary (generator p) M=z ∧
      (∀ i,0<degree i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 0)

theorem eventually_actual_even_reduction_open {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
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
  filter_upwards [eventually_actual_even_capacities (K := K) (X := X) hd] with w hw
  intro T hX hO hT extra e he
  filter_upwards [hw T hX hO hT extra e he] with v hv
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
  exact finite_even_reduction_open T hJ hdegree heven h2 hcover hv.1 hv.2.1
    (fun R _ _ _ => hv.2.2 R)

end Froberg.PreparedParameters
