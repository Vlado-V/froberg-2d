module

public import Froberg.ProductRowPairs
public import Froberg.BiformCoordinates

@[expose] public section

/-! One common coefficient space for all scalar and positive even rows.
The output spaces carry actual polynomial restrictions, including D in degree two. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}

/-- Base scalar labels and the positive-layer labels. -/
abbrev Label (q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) :=
  Fin q ⊕ ProductRows.LayerLabel J counts

/-- Full homogeneous coefficients in the prescribed output spaces. -/
abbrev Space (n d q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) :=
  (Label q J counts → Forms K n d) ×
    ((j : J) → Fin (counts j.val) → biformImage (O j.val) (Forms K n (d-j.val)))

def degree {J : Finset ℕ} {counts : ℕ → ℕ} : Label q J counts → ℕ :=
  Sum.elim (fun _ => 0) (fun a => a.1.val)

def scalar {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)} (p : Space n d q J counts O)
    (i : Label q J counts) : MvPolynomial (σ ⊕ Fin n) K :=
  rename Sum.inr (p.1 i).val

def high {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)} (p : Space n d q J counts O) :
    Label q J counts → MvPolynomial (σ ⊕ Fin n) K :=
  Sum.elim (fun _ => 0) (fun a => (p.2 a.1 a.2).val)

def generator {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)} (p : Space n d q J counts O)
    (i : Label q J counts) : MvPolynomial (σ ⊕ Fin n) K := scalar p i+high p i

/-- Extending by zero outside the active layers matches the product-row API. -/
def layers {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)} (p : Space n d q J counts O)
    (j : ℕ) (i : Fin (counts j)) : MvPolynomial (σ ⊕ Fin n) K :=
  if hj : j∈J then (p.2 ⟨j,hj⟩ i).val else 0

@[simp] theorem high_scalar_label {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)} (p : Space n d q J counts O) (i : Fin q) :
    high p (Sum.inl i)=0 := rfl

@[simp] theorem layers_active {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)} (p : Space n d q J counts O)
    (a : ProductRows.LayerLabel J counts) :
    layers p a.1.val a.2=high p (Sum.inr a) := by
  simp only [layers,dif_pos a.1.property,high,Sum.elim_inr]

/-- Every entry of the common family is a genuine total degree-d form. -/
theorem generator_homogeneous {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)}
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (p : Space n d q J counts O) (i : Label q J counts) :
    (generator p i).IsHomogeneous d := by
  apply IsHomogeneous.add
  · exact (p.1 i).property.rename_isHomogeneous
  · cases i with
    | inl i => exact isHomogeneous_zero _ _ _
    | inr a =>
      have h := biformImage_homogeneous (O a.1.val) (Forms K n (d-a.1.val))
        (hO _ a.1.property) le_rfl (p.2 a.1 a.2).property
      change (p.2 a.1 a.2).val∈homogeneousSubmodule (σ ⊕ Fin n) K d
      simpa only [Nat.add_sub_of_le (hJ _ a.1.property)] using h

/-- The whole common parameter space is finite-dimensional. -/
theorem finite_space {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (MvPolynomial σ K)}
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) :
    Module.Finite K (Space n d q J counts O) := by
  letI (j : J) : Module.Finite K (O j.val) := by
    letI : Module.Finite K (homogeneousSubmodule σ K j.val) :=
      Module.Finite.of_basis (finiteVariableFormsBasis σ j.val)
    exact Submodule.finiteDimensional_of_le (hO _ j.property)
  letI (j : J) : Module.Finite K (biformImage (O j.val) (Forms K n (d-j.val))) := by
    letI : Module.Finite K (homogeneousSubmodule (σ ⊕ Fin n) K (j.val+(d-j.val))) :=
      Module.Finite.of_basis (finiteVariableFormsBasis (σ ⊕ Fin n) (j.val+(d-j.val)))
    exact Submodule.finiteDimensional_of_le
      (biformImage_homogeneous _ _ (hO _ j.property) le_rfl)
  unfold Space
  infer_instance

end Froberg.PreparedParameters
