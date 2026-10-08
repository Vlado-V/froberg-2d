import Quartic.RationalImageAvoidance

/-!
# Composition and clearing denominators of actual rational charts

Polynomial expressions in a rational chart admit polynomial numerators with
one power of its denominator. A finite family has a common such power, and
successive rational charts compose into one rational chart on exactly the
expected nonzero-denominator domain. No parameter is added by composition.
-/
noncomputable section
namespace Quartic.RationalComposition
open MvPolynomial RationalImageAvoidance
variable {K I J L : Type*} [Field K]

/-- Clear the denominators of one polynomial evaluated on a rational chart. -/
theorem polynomial_numerator (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (f : MvPolynomial J K) :
    ∃ A : MvPolynomial I K, ∃ d : ℕ, ∀ a : I → K, eval a G ≠ 0 →
      eval (rationalMap F G a) f = eval a A / (eval a G)^d := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨A, d, hA⟩ := hf
    obtain ⟨B, e, hB⟩ := hg
    refine ⟨A * G^e + B * G^d, d + e, ?_⟩
    intro a ha
    rw [map_add, hA a ha, hB a ha]
    simp only [map_add, map_mul, map_pow, pow_add]
    field_simp
  | mul_X f j hf =>
    obtain ⟨A, d, hA⟩ := hf
    refine ⟨A * F j, d + 1, ?_⟩
    intro a ha
    rw [map_mul, hA a ha, eval_X]
    simp only [rationalMap, map_mul, pow_succ]
    exact div_mul_div_comm _ _ _ _

/-- A finite polynomial family has one common denominator exponent. -/
theorem family_numerators [Fintype L] (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (f : L → MvPolynomial J K) :
    ∃ A : L → MvPolynomial I K, ∃ d : ℕ, ∀ a : I → K, eval a G ≠ 0 →
      ∀ j, eval (rationalMap F G a) (f j) = eval a (A j) / (eval a G)^d := by
  classical
  choose A d hA using fun j => polynomial_numerator F G (f j)
  let N := ∑ j, d j
  have hle (j : L) : d j ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine ⟨fun j => A j * G^(N-d j), N, ?_⟩
  intro a ha j
  rw [hA j a ha, map_mul, map_pow]
  have hpow : (eval a G)^N = (eval a G)^(d j) * (eval a G)^(N-d j) := by
    rw [← pow_add, Nat.add_sub_of_le (hle j)]
  rw [hpow]
  exact (mul_div_mul_right _ _ (pow_ne_zero _ ha)).symm

/-- Compose actual rational charts without adding parameters. The new
principal-open domain is exactly the original domain followed by the second
chart's nonzero denominator condition. -/
theorem compose [Fintype L] (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (P : L → MvPolynomial J K) (Q : MvPolynomial J K) :
    ∃ H : L → MvPolynomial I K, ∃ D : MvPolynomial I K,
      (∀ a : I → K, eval a D ≠ 0 ↔
        eval a G ≠ 0 ∧ eval (rationalMap F G a) Q ≠ 0) ∧
      ∀ a : I → K, eval a D ≠ 0 →
        rationalMap H D a = rationalMap P Q (rationalMap F G a) := by
  classical
  let family : L ⊕ Unit → MvPolynomial J K := Sum.elim P (fun _ => Q)
  obtain ⟨A, d, hA⟩ := family_numerators F G family
  let H : L → MvPolynomial I K := fun j => A (Sum.inl j) * G
  let D := A (Sum.inr ()) * G
  have hden (a : I → K) : eval a D ≠ 0 ↔
      eval a G ≠ 0 ∧ eval (rationalMap F G a) Q ≠ 0 := by
    simp only [D, map_mul, mul_ne_zero_iff]
    constructor
    · rintro ⟨hb, hg⟩
      refine ⟨hg, ?_⟩
      rw [show Q = family (Sum.inr ()) from rfl, hA a hg]
      exact div_ne_zero hb (pow_ne_zero _ hg)
    · rintro ⟨hg, hq⟩
      refine ⟨?_, hg⟩
      rw [show Q = family (Sum.inr ()) from rfl, hA a hg] at hq
      exact (div_ne_zero_iff.mp hq).1
  refine ⟨H, D, hden, ?_⟩
  intro a ha
  obtain ⟨hg, hq⟩ := (hden a).mp ha
  funext j
  have hj := hA a hg (Sum.inl j)
  have hq' := hA a hg (Sum.inr ())
  change eval _ (P j) = _ at hj
  change eval _ Q = _ at hq'
  simp only [rationalMap, H, D, map_mul]
  rw [hj, hq', div_div_div_cancel_right₀ (pow_ne_zero d hg), mul_div_mul_right _ _ hg]

end Quartic.RationalComposition
