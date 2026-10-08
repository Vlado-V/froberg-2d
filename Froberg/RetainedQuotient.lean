import Froberg.RetainedMonomials

/-! The retained-monomial map is exactly a linear quotient by the deleted
coordinate space, and respects each homogeneous component. -/
noncomputable section
namespace Froberg
open MvPolynomial
open scoped Classical

variable {K σ : Type*} [Field K]

theorem retainMonomials_add_complement (P : (σ →₀ ℕ) → Prop)
    (f : MvPolynomial σ K) :
    retainMonomials P f + retainMonomials (fun a => ¬P a) f = f := by
  apply MvPolynomial.ext
  intro a
  rw [MvPolynomial.coeff_add, coeff_retainMonomials, coeff_retainMonomials]
  by_cases h : P a <;> simp [h]

theorem retainMonomials_complement (P : (σ →₀ ℕ) → Prop)
    (f : MvPolynomial σ K) :
    retainMonomials P (retainMonomials (fun a => ¬P a) f) = 0 := by
  ext a
  simp only [coeff_retainMonomials]
  by_cases h : P a <;> simp [h]

theorem retainMonomials_idempotent (P : (σ →₀ ℕ) → Prop)
    (f : MvPolynomial σ K) :
    retainMonomials P (retainMonomials P f) = retainMonomials P f := by
  ext a
  simp only [coeff_retainMonomials]
  by_cases h : P a <;> simp [h]

theorem ker_retainMonomials (P : (σ →₀ ℕ) → Prop) :
    (retainMonomials (K := K) P).ker =
      (retainMonomials (K := K) (fun a => ¬P a)).range := by
  ext f
  constructor
  · intro hf
    refine ⟨f, ?_⟩
    have h := retainMonomials_add_complement P f
    change retainMonomials P f = 0 at hf
    simpa only [hf, zero_add] using h
  · rintro ⟨g, rfl⟩
    exact retainMonomials_complement P g

theorem retainMonomials_homogeneous (P : (σ →₀ ℕ) → Prop)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (retainMonomials P f).IsHomogeneous d := by
  intro a ha
  apply hf
  rw [coeff_retainMonomials] at ha
  split_ifs at ha with h
  · exact ha
  · exact False.elim (ha rfl)

def retainForms {n d : ℕ} (P : (Fin n →₀ ℕ) → Prop) :
    Forms K n d →ₗ[K] Forms K n d :=
  ((retainMonomials P).comp (Forms K n d).subtype).codRestrict _
    (fun f => retainMonomials_homogeneous P f.property)

end Froberg
