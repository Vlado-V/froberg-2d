module

public import Froberg.CoefficientReconstruction
public import Froberg.BoundedWeightedComponents

@[expose] public section

/-! Actual polynomial coefficient elimination from the exact finite row conditions.
This is the scalar-plus-positive-layer part of the prepared-background argument. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ I : Type*} [Field K] [Fintype I] [LinearOrder I]

/-- Ordinary degree-d forms of a specified output weight. -/
def coefficientComponentSpace (w : σ → ℕ) (d t : ℕ) : Submodule K (MvPolynomial σ K) :=
  homogeneousSubmodule σ K d ⊓ weightedHomogeneousSubmodule K w t

/-- Exactness of all scalar/new-layer/product rows leaves precisely a scalar
cycle, modulo an explicit constant Koszul boundary of the actual generators. -/
theorem polynomial_cycle_reduces_to_scalar
    (w : σ → ℕ) (hw : ∀ x,w x≤1) (d : ℕ)
    (a E c : I → MvPolynomial σ K) (j : I → ℕ)
    (ha : ∀ i,(a i).IsHomogeneous d ∧ (a i).IsWeightedHomogeneous w 0)
    (hE : ∀ i,(E i).IsWeightedHomogeneous w (j i))
    (hEzero : ∀ i,j i=0 → E i=0) (hj : ∀ i,j i≤d)
    (hc : ∀ i,(c i).IsHomogeneous d)
    (hcycle : ∑ i,(a i+E i)*c i=0)
    (hexact : ∀ r,0<r → r≤2*d →
      CoefficientRowExact (coefficientComponentSpace w d) a E j r) :
    ∃ (M : I → I → K) (z : I → MvPolynomial σ K),
      c-matrixBoundary (fun i => a i+E i) M=z ∧
      (∀ i,0<j i → z i=0) ∧
      (∀ i,(z i).IsHomogeneous d ∧ (z i).IsWeightedHomogeneous w 0) ∧
      ∑ i,a i*z i=0 := by
  apply coefficient_rows_reduce_to_scalar_cycle (coefficientComponentSpace w d)
    a E j (fun t i => weightedHomogeneousComponent w t (c i)) d c hj hEzero
  · intro t i
    exact ⟨weightedComponent_preserves_homogeneous w (hc i) t,
      weightedHomogeneousComponent_isWeightedHomogeneous t (c i)⟩
  · exact ha
  · intro i
    exact homogeneous_eq_weightedComponents w hw (hc i)
  · intro r hr hrN
    exact mixed_cycle_row w a E c j (fun i => (ha i).2) hE hcycle r
  · exact hexact
  · exact hcycle

end Froberg
