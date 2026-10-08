import Froberg.PreparedQuadraticRow
import Froberg.PreparedFiniteRows
import Froberg.PreparedFiniteProducts

/-! Capacity records depend on output constraints only through the recorded
dimensions and the vanishing of the currently introduced higher detector. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]

theorem QuadraticRowCapacity.with_output_dimension
    {σ τ : Type*} [Fintype σ] [Fintype τ] {n d q b : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)}
    {O' : ℕ → Submodule K (MvPolynomial τ K)}
    (h : QuadraticRowCapacity n d q b J counts O)
    (hdim : finrank K (O' 2)=finrank K (O 2)) :
    QuadraticRowCapacity n d q b J counts O' where
  variables_positive := h.variables_positive
  output_positive := by simpa only [hdim] using h.output_positive
  enough_generators := h.enough_generators
  divisor_capacity := by simpa only [hdim] using h.divisor_capacity
  incidence := by simpa only [hdim] using h.incidence
  scalar_open := h.scalar_open

variable {X Y : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
  [AddCommGroup Y] [Module K Y] [Module.Finite K Y]

theorem HigherRowCapacity.with_target_dimension
    {w v d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ} {R : J}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X}
    {T' : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] Y}
    (h : HigherRowCapacity w v d q b J counts T R)
    (hdim : finrank K Y=finrank K X) (hz : T' R.val=0) :
    HigherRowCapacity w v d q b J counts T' R where
  hw := h.hw
  hv := h.hv
  positive := h.positive
  even := h.even
  degree := h.degree
  new_unconstrained := hz
  diagonal := by simpa only [hdim] using h.diagonal
  cross := by simpa only [hdim] using h.cross
  output_positive := h.output_positive
  enough_generators := h.enough_generators
  divisor_capacity := h.divisor_capacity
  incidence := h.incidence
  scalar_open := h.scalar_open

theorem ProductRowCapacity.with_target_dimension
    {w v d R : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (h : ProductRowCapacity (K := K) (X := X) w v d R J counts)
    (hdim : finrank K Y=finrank K X) :
    ProductRowCapacity (K := K) (X := Y) w v d R J counts where
  positive_output := h.positive_output
  positive_scalar := h.positive_scalar
  even_degrees := h.even_degrees
  bounded_degrees := h.bounded_degrees
  diagonal := by simpa only [hdim] using h.diagonal
  cross := by simpa only [hdim] using h.cross

end Froberg.PreparedParameters
