import Froberg.MonomialExpansion

/-! Finite monomial incidence, including the bounded multiplicity of the
three-factor map used to strengthen normalized shadow expansion. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset

/-- The finite type of exponent vectors of a fixed degree. -/
abbrev Degree (n d : ℕ) := {a : Fin n →₀ ℕ // a ∈ exponents n d}

@[simp] theorem degree_val {n d : ℕ} (a : Degree n d) : a.val.degree = d :=
  mem_exponents.mp a.property

@[simp] theorem card_degree (n d : ℕ) :
    Fintype.card (Degree n d) = (n + d - 1).choose d := by
  let e : Degree n d ≃ Sym (Fin n) d :=
    { toFun := fun a => (exponentEquiv n d).symm ⟨a.val, degree_val a⟩
      invFun := fun a => ⟨(exponentEquiv n d a).val,
        mem_exponents.mpr (exponentEquiv n d a).property⟩
      left_inv := by intro a; simp
      right_inv := by intro a; simp }
  simpa [Sym.card_sym_eq_choose] using Fintype.card_congr e

@[simp] theorem card_exponents (n d : ℕ) :
    (exponents n d).card = (n + d - 1).choose d := by
  simpa using card_degree n d

/-- Column sums of weighted incidence are independent of the source. -/
theorem sum_weight_targets {n : ℕ} (hn : 0 < n) (a : Fin n →₀ ℕ) (d : ℕ) :
    ∑ b ∈ exponents n (a.degree + d), weight b a =
      (n + a.degree + d - 1).choose d := by
  rw [← sum_weight_extensions hn a d]
  apply Finset.sum_bij_ne_zero (fun b _ _ => b - a)
  · intro b hb hw
    apply mem_exponents.mpr
    have hab := (weight_ne_zero_iff b a).mp hw
    have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hab)
    rw [map_add] at hadd
    have hd := mem_exponents.mp hb
    omega
  · intro b hb hw c hc hv heq
    have hab := (weight_ne_zero_iff b a).mp hw
    have hac := (weight_ne_zero_iff c a).mp hv
    calc
      b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
      _ = (c - a) + a := by rw [heq]
      _ = c := tsub_add_cancel_of_le hac
  · intro c hc hw
    refine ⟨a + c, mem_exponents.mpr ?_, ?_, ?_⟩
    · rw [map_add, mem_exponents.mp hc]
    · apply (weight_ne_zero_iff _ _).mpr
      exact le_add_right le_rfl
    · exact add_tsub_cancel_left a c
  · intro b hb hw
    have hab := (weight_ne_zero_iff b a).mp hw
    rw [add_tsub_cancel_of_le hab]

/-- No more than `choose(total degree,e)` distinct divisors have degree `e`. -/
theorem card_divisors_le {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) :
    ((exponents n e).filter (fun a => a ≤ b)).card ≤ b.degree.choose e := by
  rw [← sum_weight_sources b e]
  calc
    ((exponents n e).filter (fun a => a ≤ b)).card =
        ∑ a ∈ (exponents n e).filter (fun a => a ≤ b), 1 := by simp
    _ ≤ ∑ a ∈ (exponents n e).filter (fun a => a ≤ b), weight b a := by
      apply sum_le_sum
      intro a ha
      exact (weight_pos_iff b a).mpr (mem_filter.mp ha).2
    _ ≤ ∑ a ∈ exponents n e, weight b a :=
      sum_le_sum_of_subset (filter_subset _ _)

/-- Addition of fixed degrees. -/
def addDegree {n e d : ℕ} (a : Degree n e) (b : Degree n d) : Degree n (e + d) :=
  ⟨a.val + b.val, mem_exponents.mpr (by simp)⟩

/-- The degree-`e+d` upward shadow of a collection of degree-`e` monomials. -/
def shadow {n e : ℕ} (d : ℕ) (A : Finset (Degree n e)) : Finset (Degree n (e + d)) :=
  univ.filter (fun b => ∃ a ∈ A, a.val ≤ b.val)

/-- Targets divisible by a source both inside and outside the collection. -/
def mixed {n e : ℕ} (d : ℕ) (A : Finset (Degree n e)) : Finset (Degree n (e + d)) :=
  (shadow d A).filter (fun b => ∃ a : Degree n e, a ∉ A ∧ a.val ≤ b.val)

/-- Fixed-degree divisors of one monomial. -/
abbrev Divisor {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) :=
  {a : Fin n →₀ ℕ // a ∈ (exponents n e).filter (fun a => a ≤ b)}

@[simp] theorem divisor_degree {n e : ℕ} {b : Fin n →₀ ℕ} (a : Divisor b e) :
    a.val.degree = e := mem_exponents.mp (mem_filter.mp a.property).1

theorem divisor_le {n e : ℕ} {b : Fin n →₀ ℕ} (a : Divisor b e) : a.val ≤ b :=
  (mem_filter.mp a.property).2

theorem card_divisor_le {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) :
    Fintype.card (Divisor b e) ≤ b.degree.choose e := by
  simpa using card_divisors_le b e

/-- Ordered pairs of degree-`e` divisors whose sum divides the target. -/
abbrev DivisorPair {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) :=
  Σ a : Divisor b e, Divisor (b - a.val) e

theorem card_divisorPair_le {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) :
    Fintype.card (DivisorPair b e) ≤ b.degree.choose e * (b.degree - e).choose e := by
  rw [Fintype.card_sigma]
  calc
    (∑ a : Divisor b e, Fintype.card (Divisor (b - a.val) e)) ≤
        ∑ _a : Divisor b e, (b.degree - e).choose e := by
      apply sum_le_sum
      intro a _
      have hd : (b - a.val).degree = b.degree - e := by
        have h := congrArg Finsupp.degree (tsub_add_cancel_of_le (divisor_le a))
        rw [map_add, divisor_degree] at h
        omega
      simpa [hd] using card_divisor_le (b - a.val) e
    _ = Fintype.card (Divisor b e) * (b.degree - e).choose e := by simp
    _ ≤ b.degree.choose e * (b.degree - e).choose e :=
      Nat.mul_le_mul_right _ (card_divisor_le b e)

end Froberg.MonomialExpansion
