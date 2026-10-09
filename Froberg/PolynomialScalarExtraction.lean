module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic

@[expose] public section

/-!
# Recovering polynomial scalar factors from polynomial families

A scalar relating a polynomial family to a fixed nonzero polynomial vector
is itself a polynomial in the family parameters.  The proof extracts one
nonzero coefficient of the fixed vector; it requires no geometric descent.
-/

namespace Froberg

variable {k σ τ G : Type*} [Field k]

/-- A pointwise scalar factor of a polynomial family and a fixed nonzero
polynomial is a polynomial function of the parameters. -/
theorem scalar_factor_is_polynomial
    (v : MvPolynomial σ k) (hv : v ≠ 0)
    (W : MvPolynomial σ (MvPolynomial τ k))
    (x : G → τ → k) (a : G → k)
    (hrel : ∀ g, MvPolynomial.map (MvPolynomial.eval (x g)) W = MvPolynomial.C (a g) * v) :
    ∃ P : MvPolynomial τ k, ∀ g, MvPolynomial.eval (x g) P = a g := by
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hv
  refine ⟨MvPolynomial.C (v.coeff m)⁻¹ * W.coeff m, ?_⟩
  intro g
  have hc := congrArg (fun f : MvPolynomial σ k => f.coeff m) (hrel g)
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hc
  simp only [map_mul, MvPolynomial.eval_C, hc]
  field_simp

/-- Vector-valued version: a single nonzero coordinate suffices to recover
the common scalar polynomial. -/
theorem vector_scalar_factor_is_polynomial
    {ι : Type*} (v : ι → MvPolynomial σ k) (hv : v ≠ 0)
    (W : ι → MvPolynomial σ (MvPolynomial τ k))
    (x : G → τ → k) (a : G → k)
    (hrel : ∀ g i,
      MvPolynomial.map (MvPolynomial.eval (x g)) (W i) = MvPolynomial.C (a g) * v i) :
    ∃ P : MvPolynomial τ k, ∀ g, MvPolynomial.eval (x g) P = a g := by
  have hcoord : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  exact scalar_factor_is_polynomial (v i) hi (W i) x a (fun g => hrel g i)

end Froberg
