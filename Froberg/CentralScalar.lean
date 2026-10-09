module

public import Froberg.CoefficientActions

@[expose] public section

/-! # The central scalar pair on the actual coefficient space -/

noncomputable section
namespace Froberg
open Matrix Module

variable {K : Type*} [Field K] {n d r : ℕ}

/-- A scalar matrix of determinant one as a special-linear element. -/
def scalarSL (n : ℕ) (a : K) (ha : a ^ n = 1) : SpecialLinearGroup (Fin n) K :=
  ⟨a • (1 : Matrix (Fin n) (Fin n) K), by simpa [Matrix.det_smul] using ha⟩

theorem scalarSL_inverse_matrix (a : K) (ha : a ^ n = 1) (ha0 : a ≠ 0) :
    (((scalarSL n a ha)⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = a⁻¹ • 1 := by
  have hai : (a⁻¹) ^ n = 1 := by rw [inv_pow, ha, inv_one]
  have hi : (scalarSL n a ha)⁻¹ = scalarSL n a⁻¹ hai := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change (a⁻¹ • (1 : Matrix (Fin n) (Fin n) K)) * (a • 1) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  exact congrArg (fun g : SpecialLinearGroup (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K)) hi

theorem scalarSL_forms (a : K) (ha : a ^ n = 1) (p : Forms K n d) :
    slFormsEquiv (scalarSL n a ha) d p = a ^ d • p := by
  apply Subtype.ext
  exact linearSubstitution_scalar_homogeneous a p.val p.property

theorem mixFamily_scalar {V : Type*} [AddCommGroup V] [Module K V]
    (a : K) (v : Fin r → V) :
    mixFamily (a • (1 : Matrix (Fin r) (Fin r) K)) v = a • v := by
  funext i
  simp [mixFamily, Matrix.smul_apply, Matrix.one_apply]

/-- The simultaneous scalars `ζ I_n` and `ζ^d I_r` fix every coefficient
tuple; this is the central cancellation underlying the gcd divisor. -/
theorem central_pair_fixes_coefficients (ζ : K) (hζ : ζ ≠ 0)
    (hn : ζ ^ n = 1) (hr : (ζ ^ d) ^ r = 1)
    (a : CoefficientIndex n d r → K) :
    coefficientPointRepresentation (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr) a = a := by
  apply coefficientCoordinates.symm.injective
  change coefficientForms K n d r
    (coefficientPointRepresentation (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr) a) =
      coefficientForms K n d r a
  rw [coefficientPointRepresentation_forms]
  change mixFamily ((((scalarSL r (ζ ^ d) hr)⁻¹ : SpecialLinearGroup (Fin r) K) :
      Matrix (Fin r) (Fin r) K).transpose)
    (fun i => slFormsEquiv (scalarSL n ζ hn) d (coefficientForms K n d r a i)) = _
  rw [scalarSL_inverse_matrix _ hr (pow_ne_zero _ hζ),
    Matrix.transpose_smul, Matrix.transpose_one]
  simp only [scalarSL_forms]
  change mixFamily ((ζ ^ d)⁻¹ • (1 : Matrix (Fin r) (Fin r) K))
    ((ζ ^ d) • coefficientForms K n d r a) = _
  rw [mixFamily_scalar, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hζ), one_smul]

theorem central_pair_point_representation (ζ : K) (hζ : ζ ≠ 0)
    (hn : ζ ^ n = 1) (hr : (ζ ^ d) ^ r = 1) :
    coefficientPointRepresentation (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr) =
      (1 : Module.End K (CoefficientIndex n d r → K)) := by
  apply LinearMap.ext
  exact central_pair_fixes_coefficients ζ hζ hn hr

end Froberg
