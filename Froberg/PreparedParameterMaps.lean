import Froberg.PreparedParameters
import Froberg.IntrinsicBiformRow
import Froberg.ProductRowPolynomial

/-! Every row uses polynomial maps from the same actual prepared-family
coefficient space. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def scalarMap (i : Label q J counts) : Space n d q J counts O →ₗ[K] Forms K n d :=
  (LinearMap.proj i).comp (LinearMap.fst K _ _)

def layerMap (j : ℕ) (i : Fin (counts j)) :
    Space n d q J counts O →ₗ[K] MvPolynomial (σ ⊕ Fin n) K :=
  { toFun := fun p => layers p j i
    map_add' := by
      intro p p'
      classical
      by_cases hj : j∈J <;> simp [layers,hj]
    map_smul' := by
      intro c p
      classical
      by_cases hj : j∈J <;> simp [layers,hj] }

@[simp] theorem layerMap_apply (j : ℕ) (i : Fin (counts j)) (p : Space n d q J counts O) :
    layerMap j i p=layers p j i := by
  classical
  by_cases hj : j∈J <;> simp [layerMap,layers,hj]

def homogeneousLayerMap
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (j : ℕ) (i : Fin (counts j)) :
    Space n d q J counts O →ₗ[K] homogeneousSubmodule (σ ⊕ Fin n) K d :=
  (layerMap (q := q) j i).codRestrict (homogeneousSubmodule (σ ⊕ Fin n) K d) (by
    intro p
    classical
    by_cases hj : j∈J
    · change layers p j i∈homogeneousSubmodule (σ ⊕ Fin n) K d
      rw [layers,dif_pos hj]
      have hh := biformImage_homogeneous _ _ (hO j hj) le_rfl (p.2 ⟨j,hj⟩ i).property
      simpa only [Nat.add_sub_of_le (hJ j hj)] using hh
    · simp [layerMap,layers,hj])

def intrinsicLayerMap
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (i : Fin (counts R.val)) :
    Space n d q J counts O →ₗ[K] FullBiform K σ n R.val (d-R.val) :=
  (layerMap (q := q) R.val i).codRestrict (FullBiform K σ n R.val (d-R.val)) (by
    intro p
    change layers p R.val i∈FullBiform K σ n R.val (d-R.val)
    rw [layers,dif_pos R.property]
    apply mem_biformImage_of_homogeneous
    · exact biformImage_homogeneous _ _ (hO _ R.property) le_rfl (p.2 R i).property
    · exact biformImage_output_weight _ _ (hO _ R.property) (p.2 R i).property)

/-- All actual product columns are polynomial on the common parameter space. -/
theorem product_polynomial
    [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : ℕ) :
    IsPolynomialFamily (fun a : Fin (finrank K (Space n d q J counts O)) → K =>
      ProductRows.multiplication counts
        (layers ((Module.finBasis K (Space n d q J counts O)).equivFun.symm a)) J R) := by
  letI : Module.Finite K (homogeneousSubmodule (σ ⊕ Fin n) K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis (σ ⊕ Fin n) d)
  have hh := ProductRows.product_row_polynomial counts
    (homogeneousSubmodule (σ ⊕ Fin n) K d).subtype
    (fun j i a => homogeneousLayerMap (q := q) hO hJ j i ((Module.finBasis K (Space n d q J counts O)).equivFun.symm a)) J R
    (fun j hj i => isPolynomialFamily_linear
      ((homogeneousLayerMap (q := q) hO hJ j i).comp (Module.finBasis K (Space n d q J counts O)).equivFun.symm.toLinearMap))
  exact hh

end Froberg.PreparedParameters
