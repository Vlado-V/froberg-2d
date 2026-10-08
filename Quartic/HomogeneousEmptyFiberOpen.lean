import Quartic.HomogeneousMultiplicationCertificate
import Quartic.PolynomialRankOpen

/-!
# A principal open preserving an empty homogeneous projective fiber

The finite-degree certificate is derived from geometric emptiness by the
Nullstellensatz. Its full-rank determinant persists in the parameter family.
This proves empty-fiber spreading only, not positive fiber-dimension bounds.
-/
noncomputable section
namespace Quartic.HomogeneousEmptyFiberOpen
open Module MvPolynomial HomogeneousMultiplicationCertificate
variable {K : Type*} [Field K] {I : Type*} {s r : ℕ}

/-- The degree-N multiplication term is linear in the homogeneous generator. -/
def termFamily (d N : ℕ) : Forms K s d →ₗ[K] Forms K s (N-d) →ₗ[K] Forms K s N where
  toFun f := term f N
  map_add' f g := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    by_cases hd : d ≤ N <;> simp [term_val,hd,mul_add]
  map_smul' a f := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    by_cases hd : d ≤ N <;> simp [term_val,hd]

/-- All entries of the finite multiplication map vary polynomially. -/
theorem multiplication_polynomial (d : Fin r → ℕ)
    (f : ∀ j, (I → K) → Forms K s (d j))
    (hf : ∀ j, IsPolynomialFamily (f j)) (N : ℕ) :
    IsPolynomialFamily (fun p => multiplication d (fun j => f j p) N) := by
  apply isPolynomialFamily_linearMap
  intro u
  have h := IsPolynomialFamily.sum (fun j => (hf j).linear_comp ((termFamily (d j) N).flip (u j)))
  simpa only [multiplication,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    termFamily,LinearMap.flip_apply,LinearMap.coe_mk,AddHom.coe_mk] using h

/-- Geometric emptiness produces a finite multiplication determinant nonzero at the witness. -/
theorem principal_open_certificate {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin r → ℕ) (f : ∀ j, (I → K) → Forms K s (d j))
    (hf : ∀ j, IsPolynomialFamily (f j)) (p₀ : I → K)
    (hempty : ∀ x : Fin s → L, (∀ j, aeval x (f j p₀).val = 0) → x = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧
      ∀ p : I → K, eval p D ≠ 0 →
        Function.Surjective (multiplication d (fun j => f j p) N) := by
  obtain ⟨N,hN,hcert⟩ := exists_surjective_degree d (fun j => f j p₀) hempty
  obtain ⟨D,hD,hgood⟩ := rank_polynomial_principal_open
    (fun p => multiplication d (fun j => f j p) N) (multiplication_polynomial d f hf N) p₀
  refine ⟨N,hN,D,hD,?_⟩
  intro p hp
  have hr := hgood p hp
  rw [LinearMap.range_eq_top.mpr hcert,finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le _) hr

/-- The same principal open has no nonzero solution over the algebraically closed field. -/
theorem principal_open_empty_fiber {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin r → ℕ) (f : ∀ j, (I → K) → Forms K s (d j))
    (hf : ∀ j, IsPolynomialFamily (f j)) (p₀ : I → K)
    (hempty : ∀ x : Fin s → L, (∀ j, aeval x (f j p₀).val = 0) → x = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧
      ∀ p : I → K, eval p D ≠ 0 →
        ∀ x : Fin s → L, (∀ j, aeval x (f j p).val = 0) → x = 0 := by
  obtain ⟨N,hN,D,hD,hcert⟩ := principal_open_certificate d f hf p₀ hempty
  exact ⟨D,hD,fun p hp x hx => zero_of_surjective d (fun j => f j p) N hN (hcert p hp) x hx⟩

/-- Evaluation of an explicitly supplied coefficient polynomial is a polynomial scalar family. -/
theorem polynomial_eval_family (P : MvPolynomial I K) :
    IsPolynomialFamily (fun p : I → K => eval p P) := by
  intro ell
  refine ⟨C (ell 1)*P,?_⟩
  intro p
  have h := ell.map_smul (eval p P) (1 : K)
  simpa only [map_mul,eval_C,smul_eq_mul,mul_one,mul_comm,one_mul] using h.symm

/-- Specialize explicitly polynomial monomial coefficients of a homogeneous form. -/
def specialize {n : ℕ} (F : Sym (Fin s) n → MvPolynomial I K) (p : I → K) : Forms K s n :=
  ∑ e, eval p (F e) • formsBasis K s n e

/-- The explicit coefficient specialization meets the actual polynomial-family definition. -/
theorem specialize_polynomial {n : ℕ} (F : Sym (Fin s) n → MvPolynomial I K) :
    IsPolynomialFamily (specialize F) :=
  IsPolynomialFamily.sum (fun e => (polynomial_eval_family (F e)).smul
    (isPolynomialFamily_const (formsBasis K s n e)))

/-- Readable coefficient-polynomial formulation of homogeneous empty-fiber spreading. -/
theorem polynomial_coefficients_empty_fiber {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin r → ℕ) (F : ∀ j, Sym (Fin s) (d j) → MvPolynomial I K) (p₀ : I → K)
    (hempty : ∀ x : Fin s → L, (∀ j, aeval x (specialize (F j) p₀).val = 0) → x = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧
      ∀ p : I → K, eval p D ≠ 0 →
        ∀ x : Fin s → L, (∀ j, aeval x (specialize (F j) p).val = 0) → x = 0 :=
  principal_open_empty_fiber d (fun j => specialize (F j))
    (fun j => specialize_polynomial (F j)) p₀ hempty

end Quartic.HomogeneousEmptyFiberOpen
