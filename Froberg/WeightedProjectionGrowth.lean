import Mathlib

/-! Weighted incidence summation with uniformly bounded exceptional projections. -/
namespace Froberg.WeightedProjectionGrowth
open Finset

/-- A uniform row/column weighted graph converts pointwise projection estimates
and a bounded exceptional degree into a global dimension estimate. -/
theorem weighted_sum {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℕ) (ell : A → ℕ) (g : B → ℕ)
    (bad : A → Finset B) (H K R C E : ℕ)
    (hrow : ∀ a, ∑ b, w a b = R)
    (hcol : ∀ b, ∑ a, w a b = C)
    (hcard : ∀ a, (bad a).card ≤ E)
    (hgood : ∀ a b, b ∉ bad a → (H-K)*w a b*ell a ≤ H*w a b*g b) :
    (H-K)*R*(∑ a, ell a) ≤ H*C*((∑ b, g b)+E*(∑ a, ell a)) := by
  classical
  have hw : ∀ a b, w a b ≤ C := by
    intro a b
    rw [← hcol b]
    exact single_le_sum (f := fun a => w a b) (fun _ _ => Nat.zero_le _) (mem_univ a)
  have hbad : ∀ a, ∑ b ∈ bad a, w a b ≤ C*E := by
    intro a
    calc
      _ ≤ ∑ _b ∈ bad a, C := sum_le_sum (fun b _ => hw a b)
      _ = (bad a).card*C := by simp
      _ ≤ E*C := Nat.mul_le_mul_right C (hcard a)
      _ = C*E := Nat.mul_comm _ _
  have hp : ∀ a b, (H-K)*w a b*ell a ≤
      H*w a b*g b + if b ∈ bad a then H*w a b*ell a else 0 := by
    intro a b
    by_cases hb : b ∈ bad a
    · rw [if_pos hb]
      have hh := Nat.mul_le_mul_right (w a b*ell a) (Nat.sub_le H K)
      have hh' : (H-K)*w a b*ell a ≤ H*w a b*ell a := by
        simpa only [mul_assoc] using hh
      exact hh'.trans (Nat.le_add_left _ _)
    · rw [if_neg hb,add_zero]
      exact hgood a b hb
  have hr : ∀ a, (H-K)*R*ell a ≤ H*(∑ b, w a b*g b) + H*C*E*ell a := by
    intro a
    have hh := sum_le_sum (fun b (_ : b ∈ (univ : Finset B)) => hp a b)
    simp only [sum_add_distrib,← mul_sum,← sum_mul,hrow] at hh
    have hbe : (∑ b : B, if b ∈ bad a then H*w a b*ell a else 0) =
        H*(∑ b ∈ bad a, w a b)*ell a := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter,← sum_mul,← mul_sum]
    rw [hbe] at hh
    have he := Nat.mul_le_mul_left H (Nat.mul_le_mul_right (ell a) (hbad a))
    have hs : (∑ b : B,H*w a b*g b) = H*(∑ b,w a b*g b) := by
      simp only [mul_sum,mul_assoc]
    rw [hs] at hh
    have he' : H*(∑ b ∈ bad a,w a b)*ell a ≤ H*C*E*ell a := by
      simpa only [mul_assoc] using he
    exact hh.trans (Nat.add_le_add_left he' _)
  have hh := sum_le_sum (fun a (_ : a ∈ (univ : Finset A)) => hr a)
  have he : (∑ a : A, ∑ b : B, w a b*g b) = C*∑ b, g b := by
    rw [sum_comm]
    simp only [← sum_mul,hcol,← mul_sum]
  simp only [sum_add_distrib,← mul_sum] at hh
  rw [he] at hh
  simpa only [mul_add,mul_assoc] using hh

/-- A target whose quotient dimension is at least H-K retains this fraction
of any source dimension at most H whenever its projection has maximal rank. -/
theorem capacity_fraction {H K ell c g : ℕ} (hell : ell ≤ H) (hc : H-K ≤ c)
    (hg : min ell c ≤ g) : (H-K)*ell ≤ H*g := by
  rcases le_total ell c with hl | hl
  · rw [min_eq_left hl] at hg
    exact (Nat.mul_le_mul_right ell (Nat.sub_le H K)).trans (Nat.mul_le_mul_left H hg)
  · rw [min_eq_right hl] at hg
    calc
      (H-K)*ell ≤ (H-K)*H := Nat.mul_le_mul_left _ hell
      _ ≤ c*H := Nat.mul_le_mul_right H hc
      _ ≤ g*H := Nat.mul_le_mul_right H hg
      _ = H*g := Nat.mul_comm _ _

end Froberg.WeightedProjectionGrowth
