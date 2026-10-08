import Froberg.GenericDimensions

/-!
# Reducing equivariant divisibility to the generic cokernel

The weighted Euler characteristic already has the required gcd divisor.
Consequently the genuine generic Euler identity transfers divisibility
from the cokernel to the first homology dimension.
-/

namespace Froberg

/-- The dimension of a symmetric power has the central-weight divisor. -/
theorem variables_dvd_degree_mul_monomials (n k : ℕ) :
    n ∣ k * (n + k - 1).choose k := by
  by_cases hk : k = 0
  · simp [hk]
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
  have hsub : n + k - 1 - (k - 1) = n := by omega
  have heq := Nat.choose_succ_right_eq (n + k - 1) (k - 1)
  rw [hsucc, hsub] at heq
  exact ⟨(n + k - 1).choose (k - 1), by simpa only [Nat.mul_comm] using heq⟩

/-- Twice the exterior-square dimension is the ordered-pair count. -/
theorem twice_choose_two (r : ℕ) : 2 * r.choose 2 = r * (r - 1) := by
  simpa only [Nat.choose_one_right, Nat.mul_comm] using Nat.choose_succ_right_eq r 1

/-- The full weighted Euler characteristic is divisible before using any
generic-rank or group-action argument. -/
theorem gcd_dvd_weighted_euler (n d r : ℕ) :
    (Nat.gcd n (d * r) : ℤ) ∣ (2 * d : ℤ) * euler n d r := by
  let g := Nat.gcd n (d * r)
  have h₀ : g ∣ (2 * d) * (n + 2 * d - 1).choose (2 * d) :=
    (Nat.gcd_dvd_left n (d * r)).trans (variables_dvd_degree_mul_monomials n (2 * d))
  have hd : g ∣ d * (n + d - 1).choose d :=
    (Nat.gcd_dvd_left n (d * r)).trans (variables_dvd_degree_mul_monomials n d)
  have h₁ : g ∣ (2 * d) * r * (n + d - 1).choose d := by
    convert dvd_mul_of_dvd_right hd (2 * r) using 1 <;> ring
  have h₂ : g ∣ (2 * d) * r.choose 2 := by
    have hh := dvd_mul_of_dvd_left (Nat.gcd_dvd_right n (d * r)) (r - 1)
    convert hh using 1
    rw [show 2 * d * r.choose 2 = d * (2 * r.choose 2) by ring, twice_choose_two]
    ring
  have h₀' : (g : ℤ) ∣ (2 * d : ℤ) * ((n + 2 * d - 1).choose (2 * d) : ℤ) := by
    exact_mod_cast h₀
  have h₁' : (g : ℤ) ∣ (2 * d : ℤ) * r * ((n + d - 1).choose d : ℤ) := by
    exact_mod_cast h₁
  have h₂' : (g : ℤ) ∣ (2 * d : ℤ) * (r.choose 2 : ℤ) := by
    exact_mod_cast h₂
  convert dvd_add (dvd_sub h₀' h₁') h₂' using 1 <;> unfold euler <;> ring

/-- Cokernel divisibility implies the corresponding divisibility of the
actual generic first homology via its already proved Euler identity. -/
theorem genericHomology_divisibility_of_genericCokernel
    {K : Type*} [Field K] [Infinite K] {n d r : ℕ}
    (hn : 0 < n) (hr : r ≤ (n + d - 1).choose d)
    (hc : Nat.gcd n (d * r) ∣ (2 * d) * genericCokernel K n d r) :
    Nat.gcd n (d * r) ∣ (2 * d) * genericHomology K n d r := by
  have hc' : (Nat.gcd n (d * r) : ℤ) ∣
      (2 * d : ℤ) * (genericCokernel K n d r : ℤ) := by exact_mod_cast hc
  have he := gcd_dvd_weighted_euler n d r
  have hid := generic_euler (K := K) hn hr
  have hh : (Nat.gcd n (d * r) : ℤ) ∣
      (2 * d : ℤ) * (genericHomology K n d r : ℤ) := by
    convert dvd_sub hc' he using 1
    rw [← hid]
    ring
  exact_mod_cast hh

end Froberg
