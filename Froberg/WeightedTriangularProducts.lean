module

public import Froberg.LowHomogeneousProduct

@[expose] public section

/-! Actual homogeneous components of products with prepared generators.
Lower output-degree terms contribute only below the homogeneous target row. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ : Type*} [Field K]

/-- Multiplication by a weighted-homogeneous coefficient shifts the component
index by its degree. The other factor may have arbitrary lower terms. -/
theorem weighted_component_mul_homogeneous (w : σ → ℕ)
    (p q : MvPolynomial σ K) (a b : ℕ) (hq : q.IsWeightedHomogeneous w b) :
    weightedHomogeneousComponent w (a+b) (p*q) =
      weightedHomogeneousComponent w a p*q := by
  classical
  rw [weightedHomogeneousComponent_product]
  rw [Finset.sum_eq_single (a,b)]
  · rw [hq.weightedHomogeneousComponent_same]
  · intro ij hij hne
    have hb : ij.2 ≠ b := by
      intro he
      apply hne
      have hs := Finset.mem_antidiagonal.mp hij
      exact Prod.ext (by omega) he
    rw [hq.weightedHomogeneousComponent_ne _ hb,mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim

/-- An upper degree bound on a generator gives the exact upper support bound
on its product with a homogeneous coefficient. -/
theorem weighted_component_product_above (w : σ → ℕ)
    (p q : MvPolynomial σ K) (j b t : ℕ)
    (hp : ∀ k, j<k → weightedHomogeneousComponent w k p=0)
    (hq : q.IsWeightedHomogeneous w b) (ht : j+b<t) :
    weightedHomogeneousComponent w t (p*q)=0 := by
  have he : t=(t-b)+b := by omega
  rw [he,weighted_component_mul_homogeneous w p q (t-b) b hq,
    hp (t-b) (by omega),zero_mul]

/-- The top row of a product depends only on the top component of the
prepared generator, so every lower perturbation disappears there. -/
theorem weighted_component_product_top (w : σ → ℕ)
    (p high q : MvPolynomial σ K) (j b : ℕ)
    (hp : weightedHomogeneousComponent w j p=high)
    (hq : q.IsWeightedHomogeneous w b) :
    weightedHomogeneousComponent w (j+b) (p*q)=high*q := by
  rw [weighted_component_mul_homogeneous w p q j b hq,hp]

/-- A scalar shift and a positive weighted-degree piece have exactly the
required top component and upper support. -/
theorem scalar_shift_top_components (w : σ → ℕ)
    (scalar high : MvPolynomial σ K) {j : ℕ} (hj : 0<j)
    (hs : scalar.IsWeightedHomogeneous w 0) (hh : high.IsWeightedHomogeneous w j) :
    weightedHomogeneousComponent w j (scalar+high)=high ∧
      ∀ k, j<k → weightedHomogeneousComponent w k (scalar+high)=0 := by
  constructor
  · rw [map_add,hs.weightedHomogeneousComponent_ne _ (by omega),
      hh.weightedHomogeneousComponent_same,zero_add]
  · intro k hk
    rw [map_add,hs.weightedHomogeneousComponent_ne _ (by omega),
      hh.weightedHomogeneousComponent_ne _ (by omega),add_zero]

end Froberg
