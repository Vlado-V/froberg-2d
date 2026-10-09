module

public import Froberg.OrderedMonomials
public import Froberg.Prefix
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

/-! Canonical monomial coordinates for a vector space tensored with forms.
The ordered coordinates use the same multiplicative monomial order as the
initial-subspace construction. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
open Quartic.HomogeneousCoefficientCoordinates
open AttachedMultiplication
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {m e : ℕ}

local instance tensorFormGroup : AddCommGroup (V ⊗[K] Forms K m e) :=
  Module.addCommMonoidToAddCommGroup K

/-- Literal monomial coefficients with values in V. -/
def tensorFormCoordinates : (V ⊗[K] Forms K m e) ≃ₗ[K] (Exponent m e → V) :=
  (TensorProduct.congr (LinearEquiv.refl K V) equiv).trans
    (TensorProduct.piScalarRight K K V (Exponent m e))

@[simp] theorem tensorFormCoordinates_tmul (v : V) (p : Forms K m e)
    (a : Exponent m e) :
    tensorFormCoordinates (v ⊗ₜ[K] p) a = p.val.coeff a.val • v := by
  simp [tensorFormCoordinates]

@[simp] theorem tensorFormCoordinates_monomial (v : V) (a : Exponent m e) :
    tensorFormCoordinates (v ⊗ₜ[K] monomialForm a) = Pi.single a v := by
  classical
  funext b
  rw [tensorFormCoordinates_tmul]
  by_cases h : b=a
  · subst b; simp [monomialForm]
  · have hv : a.val ≠ b.val := fun hh => h (Subtype.ext hh.symm)
    simp [monomialForm,coeff_monomial,hv,Pi.single_eq_of_ne h]

@[simp] theorem tensorFormCoordinates_symm_single (v : V) (a : Exponent m e) :
    tensorFormCoordinates.symm (Pi.single a v) = v ⊗ₜ[K] monomialForm a := by
  apply tensorFormCoordinates.injective
  rw [LinearEquiv.apply_symm_apply,tensorFormCoordinates_monomial]

/-- The same coordinates in increasing monomial order. -/
def orderedTensorFormCoordinates : (V ⊗[K] Forms K m e) ≃ₗ[K]
    (Fin (Fintype.card (Exponent m e)) → V) :=
  tensorFormCoordinates.trans
    (LinearEquiv.piCongrLeft' K (fun _ : Exponent m e => V) (OrderedMonomials.enumerate m e).symm)

@[simp] theorem orderedTensorFormCoordinates_apply (z : V ⊗[K] Forms K m e)
    (i : Fin (Fintype.card (Exponent m e))) :
    orderedTensorFormCoordinates z i =
      tensorFormCoordinates z (OrderedMonomials.enumerate m e i) := rfl

@[simp] theorem orderedTensorFormCoordinates_monomial
    (v : V) (a : Exponent m e) :
    orderedTensorFormCoordinates (v ⊗ₜ[K] monomialForm a) =
      Pi.single ((OrderedMonomials.enumerate m e).symm a) v := by
  classical
  funext i
  rw [orderedTensorFormCoordinates_apply,tensorFormCoordinates_monomial]
  by_cases h : i=(OrderedMonomials.enumerate m e).symm a
  · subst i; simp
  · have hi : OrderedMonomials.enumerate m e i ≠ a := by
      intro hi
      apply h
      exact (OrderedMonomials.enumerate m e).injective (by simpa using hi)
    simp [Pi.single_eq_of_ne h,Pi.single_eq_of_ne hi]

@[simp] theorem orderedTensorFormCoordinates_symm_single
    (v : V) (i : Fin (Fintype.card (Exponent m e))) :
    orderedTensorFormCoordinates.symm (Pi.single i v) =
      v ⊗ₜ[K] monomialForm (OrderedMonomials.enumerate m e i) := by
  apply orderedTensorFormCoordinates.injective
  rw [LinearEquiv.apply_symm_apply,orderedTensorFormCoordinates_monomial]
  simp

variable {B W : Type*} [AddCommGroup B] [Module K B] [AddCommGroup W] [Module K W]
variable {d : ℕ}

/-- The genuine tensor product of a bilinear map with homogeneous multiplication. -/
def tensorFormProduct (μ : B →ₗ[K] V →ₗ[K] W) :
    (B ⊗[K] Forms K m d) →ₗ[K] (V ⊗[K] Forms K m e) →ₗ[K]
      (W ⊗[K] Forms K m (e+d)) :=
  TensorProduct.map₂ μ (gradedMultiplication (d := e) (e := d)).flip

@[simp] theorem tensorFormProduct_tmul (μ : B →ₗ[K] V →ₗ[K] W)
    (b : B) (v : V) (p : Forms K m d) (q : Forms K m e) :
    tensorFormProduct μ (b ⊗ₜ[K] p) (v ⊗ₜ[K] q) =
      μ b v ⊗ₜ[K] gradedMultiplication q p := rfl

@[simp] theorem gradedMultiplication_monomial (a : Exponent m e) (b : Exponent m d) :
    gradedMultiplication (K := K) (monomialForm a) (monomialForm b) = monomialForm (addExponent a b) := by
  apply Subtype.ext
  simp [gradedMultiplication,monomialForm,addExponent,monomial_mul_monomial]

/-- Multiplication conjugated into ordered, vector-valued monomial coordinates. -/
def orderedTensorFormProduct (μ : B →ₗ[K] V →ₗ[K] W) :
    (Exponent m d → B) →ₗ[K]
      (Fin (Fintype.card (Exponent m e)) → V) →ₗ[K]
        (Fin (Fintype.card (Exponent m (e+d))) → W) where
  toFun f := orderedTensorFormCoordinates.toLinearMap.comp
    ((tensorFormProduct μ (tensorFormCoordinates.symm f)).comp
      orderedTensorFormCoordinates.symm.toLinearMap)
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

@[simp] theorem orderedTensorFormProduct_single (μ : B →ₗ[K] V →ₗ[K] W)
    (a : Exponent m d) (j : Fin (Fintype.card (Exponent m e))) (b : B) (v : V) :
    orderedTensorFormProduct μ (Pi.single a b) (Pi.single j v) =
      Pi.single (OrderedMonomials.shift a j) (μ b v) := by
  simp [orderedTensorFormProduct,OrderedMonomials.shift]

end Froberg
