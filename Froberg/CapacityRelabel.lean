import Froberg.PreparedFiniteProducts
import Froberg.PreparedQuadraticRow
import Froberg.PreparedFiniteRows

/-! Capacity records depend on the scalar-label cardinality and the actual
new-row count, so adding zero-count labels changes no incidence input. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

 theorem QuadraticRowCapacity.with_labels {n d q q' b : ℕ}
    {J J' : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (MvPolynomial σ K)}
    (h : QuadraticRowCapacity n d q b J c O)
    (hcard : Fintype.card (Label q' J' c')=Fintype.card (Label q J c))
    (hc : c' 2=c 2) : QuadraticRowCapacity n d q' b J' c' O := by
  refine { variables_positive := h.variables_positive
           output_positive := h.output_positive
           enough_generators := ?_
           divisor_capacity := h.divisor_capacity
           incidence := ?_
           scalar_open := ?_ }
  · simpa only [hc] using h.enough_generators
  · simpa only [hcard] using h.incidence
  · rw [hcard]
    exact h.scalar_open

 theorem HigherRowCapacity.with_labels {w v d q q' b : ℕ}
    {J J' : Finset ℕ} {c c' : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X} {R : J} {R' : J'}
    (h : HigherRowCapacity w v d q b J c T R)
    (hR : R'.val=R.val)
    (hcard : Fintype.card (Label q' J' c')=Fintype.card (Label q J c))
    (hc : c' R'.val=c R.val)
    (hp : ProductRowCapacity (K := K) (X := X) w v d R'.val J' c')
    (hpositive : ∀ j∈J',0<j) : HigherRowCapacity w v d q' b J' c' T R' := by
  refine { hw := h.hw
           hv := h.hv
           positive := hpositive
           even := hp.even_degrees
           degree := hp.bounded_degrees
           new_unconstrained := ?_
           diagonal := hp.diagonal
           cross := hp.cross
           output_positive := ?_
           enough_generators := ?_
           divisor_capacity := ?_
           incidence := ?_
           scalar_open := ?_ }
  · simpa only [hR] using h.new_unconstrained
  · simpa only [hR] using h.output_positive
  · rw [hc,hR]
    exact h.enough_generators
  · simpa only [hR] using h.divisor_capacity
  · simpa only [hR,hcard] using h.incidence
  · rw [hR,hcard]
    exact h.scalar_open

end Froberg.PreparedParameters
