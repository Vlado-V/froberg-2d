import Froberg.VandermondeProducts
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # The actual symmetric-power convolution map -/

noncomputable section
namespace Froberg
open Finset TensorProduct

variable {K : Type*} [Field K]

abbrev BiformAlgebra (K : Type*) [Field K] (a m : ℕ) := Poly K a ⊗[K] Poly K m

/-- Coefficients of the identity `v(t)y(t)`. -/
def convolutionCoefficient (a m : ℕ) (j : Fin (m + a - 1)) : BiformAlgebra K a m :=
  ∑ i : Fin a, ∑ k : Fin m,
    if (i : ℕ) + (k : ℕ) = (j : ℕ) then
      MvPolynomial.X i ⊗ₜ[K] MvPolynomial.X k else 0

/-- The homomorphism sending each convolution variable to its actual bilinear coefficient. -/
def convolutionHom (a m : ℕ) : Poly K (m + a - 1) →ₐ[K] BiformAlgebra K a m :=
  MvPolynomial.aeval (convolutionCoefficient a m)

private theorem convolution_inner_sum {a m : ℕ} (t : K) (i : Fin a) (k : Fin m)
    (z : BiformAlgebra K a m) :
    (∑ j : Fin (m + a - 1), if (i : ℕ) + (k : ℕ) = (j : ℕ) then
      t ^ (j : ℕ) • z else 0) = t ^ ((i : ℕ) + (k : ℕ)) • z := by
  let j₀ : Fin (m + a - 1) := ⟨i.val + k.val, by omega⟩
  rw [Finset.sum_eq_single j₀]
  · simp [j₀]
  · intro j hj hne
    have hh : ¬(i : ℕ) + (k : ℕ) = (j : ℕ) := by
      intro h
      exact hne (Fin.ext h.symm)
    simp [hh]
  · simp

/-- Convolution sends the moment linear form to the separated product. -/
theorem convolutionHom_momentLinear (a m : ℕ) (t : K) :
    convolutionHom a m (momentLinear (m + a - 1) t) =
      momentLinear a t ⊗ₜ[K] momentLinear m t := by
  simp only [momentLinear, convolutionHom, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, ← Algebra.smul_def]
  simp only [convolutionCoefficient, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  trans ∑ i : Fin a, ∑ k : Fin m, t ^ ((i : ℕ) + (k : ℕ)) •
    (MvPolynomial.X i ⊗ₜ[K] MvPolynomial.X k)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    exact convolution_inner_sum t i k _
  · simp only [← MvPolynomial.smul_eq_C_mul, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, pow_add]
    simp only [Finset.smul_sum, ← TensorProduct.smul_tmul', smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]

/-- Restriction of convolution followed by scalar multiplication, with its
full symmetric-power source. -/
def symmetricConvolutionMap (a e m : ℕ) :
    (Forms K (m + a - 1) e ⊗[K] Forms K m (a - 1)) →ₗ[K] BiformAlgebra K a m :=
  (LinearMap.mul' K (BiformAlgebra K a m)).comp
    (TensorProduct.map
      ((convolutionHom (K := K) a m).toLinearMap.comp
        (MvPolynomial.homogeneousSubmodule (Fin (m + a - 1)) K e).subtype)
      ((Algebra.TensorProduct.includeRight : Poly K m →ₐ[K] BiformAlgebra K a m).toLinearMap.comp
        (MvPolynomial.homogeneousSubmodule (Fin m) K (a - 1)).subtype))

@[simp] theorem symmetricConvolutionMap_tmul (a e m : ℕ)
    (f : Forms K (m + a - 1) e) (g : Forms K m (a - 1)) :
    symmetricConvolutionMap a e m (f ⊗ₜ[K] g) =
      convolutionHom a m f.val * (1 ⊗ₜ[K] g.val) := by
  simp [symmetricConvolutionMap]

end Froberg
