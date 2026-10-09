module

public import Froberg.EquivariantUnits
public import Froberg.PrimitiveVectors
public import Froberg.PolynomialScalarExtraction
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

/-!
# Polynomial actions on primitive rational lines

This is an algebraic replacement for the determinant-line trivialization
step.  An invariant rational line in a polynomial module, acted on by
invertible semilinear coordinate changes, has a primitive representative
fixed by a polynomial special-linear-group action.
-/

namespace Froberg

open Matrix

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- Inversion on `SL` is polynomial: substitute the adjugate of the generic
matrix into a coordinate polynomial. -/
theorem slPolynomialEval_inverse_polynomial (P : MvPolynomial (ι × ι) k) :
    ∃ Q : MvPolynomial (ι × ι) k,
      ∀ g : Matrix.SpecialLinearGroup ι k,
        slPolynomialEval Q g = slPolynomialEval P g⁻¹ := by
  let X : Matrix ι ι (MvPolynomial (ι × ι) k) := Matrix.mvPolynomialX ι ι k
  let invEntry : ι × ι → MvPolynomial (ι × ι) k := fun ij => X.adjugate ij.1 ij.2
  refine ⟨MvPolynomial.bind₁ invEntry P, ?_⟩
  intro g
  unfold slPolynomialEval
  change MvPolynomial.eval₂Hom (RingHom.id k) _ (MvPolynomial.bind₁ invEntry P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply congrArg (fun f : ι × ι → k => MvPolynomial.eval₂Hom (RingHom.id k) f P)
  funext ij
  have heval := (MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2)).map_adjugate X
  have hX : (MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2)).mapMatrix X =
      (g : Matrix ι ι k) := by
    ext i j
    simp [X, Matrix.mvPolynomialX]
  rw [hX] at heval
  exact congrArg (fun M : Matrix ι ι k => M ij.1 ij.2) heval

variable [Infinite k]

/-- Every polynomial multiplicative character of `SL` is trivial.  The
polynomial reciprocal follows from the adjugate formula for inversion. -/
theorem sl_polynomial_character_trivial
    (χ : Matrix.SpecialLinearGroup ι k →* k)
    (P : MvPolynomial (ι × ι) k)
    (hP : ∀ g, slPolynomialEval P g = χ g) :
    ∀ g, χ g = 1 := by
  obtain ⟨Q, hQ⟩ := slPolynomialEval_inverse_polynomial P
  have hinv : ∀ g, slPolynomialEval P g * slPolynomialEval Q g = 1 := by
    intro g
    rw [hQ, hP, hP, ← map_mul, mul_inv_cancel, map_one]
  intro g
  rw [← hP, slPolynomialUnit_constant P Q hinv g, hP, map_one]

omit [Fintype ι] [DecidableEq ι] [Infinite k] in
/-- Scalars on an invariant nonzero vector form a character. -/
theorem representation_scalar_character
    {G V : Type*} [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (v : V) (hv : v ≠ 0)
    (hline : ∀ g, ∃ a : k, ρ g v = a • v) :
    ∃ χ : G →* k, ∀ g, ρ g v = χ g • v := by
  choose a ha using hline
  have hone : a 1 = 1 := by
    apply smul_left_injective k hv
    change a 1 • v = 1 • v
    rw [← ha, map_one, Module.End.one_apply, one_smul]
  have hmul : ∀ g h, a (g * h) = a g * a h := by
    intro g h
    apply smul_left_injective k hv
    change a (g * h) • v = (a g * a h) • v
    rw [← ha, map_mul, Module.End.mul_apply, ha h, map_smul, ha g, smul_smul]
    rw [mul_comm]
  exact ⟨{ toFun := a, map_one' := hone, map_mul' := hmul }, ha⟩

/-- A polynomial special-linear-group action fixes every nonzero vector
whose ground-field line it preserves. -/
theorem polynomial_sl_invariant_line_fixed
    {σ J : Type*}
    (ρ : Representation k (Matrix.SpecialLinearGroup ι k)
      (J → MvPolynomial σ k))
    (v : J → MvPolynomial σ k) (hv : v ≠ 0)
    (hline : ∀ g, ∃ a : k, ρ g v = a • v)
    (W : J → MvPolynomial σ (MvPolynomial (ι × ι) k))
    (hW : ∀ g i, MvPolynomial.map
      (MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2)) (W i) = (ρ g v) i) :
    ∀ g, ρ g v = v := by
  obtain ⟨χ, hχ⟩ := representation_scalar_character ρ v hv hline
  have hpoly : ∀ g i, MvPolynomial.map
      (MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2)) (W i) =
      MvPolynomial.C (χ g) * v i := by
    intro g i
    rw [hW, hχ]
    simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul]
  obtain ⟨P, hP⟩ := vector_scalar_factor_is_polynomial v hv W
    (fun (g : Matrix.SpecialLinearGroup ι k) ij => g ij.1 ij.2) χ hpoly
  have hχone := sl_polynomial_character_trivial χ P hP
  intro g
  rw [hχ, hχone, one_smul]

/-- The same fixed-line conclusion for the product of the two special
linear groups appearing in the universal multiplication complex.  It
suffices that each factor acts polynomially. -/
theorem polynomial_sl_product_invariant_line_fixed
    {κ σ J : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Representation k
      (Matrix.SpecialLinearGroup ι k × Matrix.SpecialLinearGroup κ k)
      (J → MvPolynomial σ k))
    (v : J → MvPolynomial σ k) (hv : v ≠ 0)
    (hline : ∀ g, ∃ a : k, ρ g v = a • v)
    (W₁ : J → MvPolynomial σ (MvPolynomial (ι × ι) k))
    (W₂ : J → MvPolynomial σ (MvPolynomial (κ × κ) k))
    (hW₁ : ∀ g i, MvPolynomial.map
      (MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2)) (W₁ i) = (ρ (g, 1) v) i)
    (hW₂ : ∀ g i, MvPolynomial.map
      (MvPolynomial.eval (fun ij : κ × κ => g ij.1 ij.2)) (W₂ i) = (ρ (1, g) v) i) :
    ∀ g, ρ g v = v := by
  have h₁ : ∀ g : Matrix.SpecialLinearGroup ι k, ρ (g, 1) v = v :=
    polynomial_sl_invariant_line_fixed
      (ρ.comp (MonoidHom.inl _ _)) v hv (fun g => hline (g, 1)) W₁ hW₁
  have h₂ : ∀ g : Matrix.SpecialLinearGroup κ k, ρ (1, g) v = v :=
    polynomial_sl_invariant_line_fixed
      (ρ.comp (MonoidHom.inr _ _)) v hv (fun g => hline (1, g)) W₂ hW₂
  intro g
  have hg : g = (g.1, 1) * (1, g.2) := by simp
  rw [hg, map_mul, Module.End.mul_apply, h₂, h₁]

/-- Primitive normalization upgrades invariance of a fraction-field line
to a fixed polynomial vector.  The action is given by coefficient-ring
automorphisms and invertible matrices, and its coefficients are polynomial
functions of the special-linear matrix entries. -/
theorem polynomial_sl_primitive_rational_line_fixed
    {σ F : Type*} [Field F]
    [Algebra (MvPolynomial σ k) F] [IsFractionRing (MvPolynomial σ k) F]
    {J : Type*} [Fintype J] [DecidableEq J]
    (ρ : Representation k (Matrix.SpecialLinearGroup ι k)
      (J → MvPolynomial σ k))
    (v : J → MvPolynomial σ k) (hv : v ≠ 0) (hprim : IsPrimitiveVector v)
    (e : Matrix.SpecialLinearGroup ι k → MvPolynomial σ k ≃+* MvPolynomial σ k)
    (A B : Matrix.SpecialLinearGroup ι k → Matrix J J (MvPolynomial σ k))
    (hBA : ∀ g, B g * A g = 1)
    (haction : ∀ g, ρ g v = A g *ᵥ (fun i => e g (v i)))
    (hline : ∀ g, ∃ c : F, ∀ i,
      algebraMap (MvPolynomial σ k) F ((ρ g v) i) =
        c * algebraMap (MvPolynomial σ k) F (v i))
    (W : J → MvPolynomial σ (MvPolynomial (ι × ι) k))
    (hW : ∀ g i, MvPolynomial.map
      (MvPolynomial.eval (fun ij : ι × ι => g ij.1 ij.2)) (W i) = (ρ g v) i) :
    ∀ g, ρ g v = v := by
  apply polynomial_sl_invariant_line_fixed ρ v hv _ W hW
  intro g
  have hprim' : IsPrimitiveVector (ρ g v) := by
    rw [haction]
    exact (hprim.map (e g)).mulVec (A g) (B g) (hBA g)
  obtain ⟨c, hc⟩ := hline g
  obtain ⟨a, _, _, ha⟩ := primitive_polynomial_vectors_constant_scalar
    v (ρ g v) hprim hprim' c hc
  refine ⟨a, ?_⟩
  funext i
  simpa only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul] using ha i

end Froberg
