module

public import Froberg.PreparedProductOpen
public import Froberg.BiformKernelIntersection
public import Froberg.BalancedProductRow

@[expose] public section

/-! Explicit finite diagonal and cross capacities provide the remaining
product-row witnesses in the common prepared-family coefficient space. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

structure ProductRowCapacity (w v d R : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) : Prop where
  positive_output : 0<w
  positive_scalar : 0<v
  even_degrees : ∀ j∈J,Even j
  bounded_degrees : ∀ j∈J,j≤d
  diagonal : ∀ r : ProductRows.Row J R,r.val.val=R-r.val.val →
    counts r.val.val≤(w.choose r.val.val-finrank K X)*(v.choose (d-r.val.val)/2)
  cross : ∀ r : ProductRows.Row J R,r.val.val≠R-r.val.val →
    counts r.val.val≤((w+r.val.val-1).choose r.val.val-finrank K X)*(v+(d-r.val.val)-1).choose (d-r.val.val) ∧
    counts (R-r.val.val)≤((w+(R-r.val.val)-1).choose (R-r.val.val)-finrank K X)*
      (v+(d-(R-r.val.val))-1).choose (d-(R-r.val.val))

/-- The four-block construction is a point of the literal prepared parameter
space, with no condition on its scalar component. -/
theorem exists_product_row_parameter {w v d R q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hcap : ProductRowCapacity (K := K) (X := X) w v d R J counts) :
    ∃ p : Space (v+v) d q J counts (constrainedOutputs T),
      Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  obtain ⟨E,hE,hEI⟩ := ProductRows.exists_balanced_product_row
    hcap.positive_output hcap.positive_scalar J counts hcap.even_degrees
    hcap.bounded_degrees T hcap.diagonal hcap.cross
  have hmem : ∀ j∈J,∀ i,E j i∈biformImage (constrainedOutputs T j) (Forms K (v+v) (d-j)) := by
    intro j hj i
    apply mem_biformImage_inf_kernel
    · apply mem_biformImage_of_homogeneous
      · simpa only [Nat.add_sub_of_le (hcap.bounded_degrees j hj)] using (hE j i).1
      · exact (hE j i).2.1
    · exact (hE j i).2.2.2.2
  refine ⟨ofPolynomialFamilies 0 E hmem,?_⟩
  rw [products_ofPolynomialFamilies]
  exact hEI

end Froberg.PreparedParameters
