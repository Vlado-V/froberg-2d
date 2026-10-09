module

public import Froberg.Graded
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! Finite-dimensional Euler characteristic and the two-critical-count reduction.
The reduction states its monotonicity hypotheses explicitly. -/
noncomputable section
namespace Froberg
open Module

section Complex
variable {K B A T : Type*} [Field K]
  [AddCommGroup B] [Module K B]
  [AddCommGroup A] [Module K A] [Module.Finite K A]
  [AddCommGroup T] [Module K T] [Module.Finite K T]

/-- The boundary map with its codomain restricted to cycles. -/
def boundaryToCycles (δ : B →ₗ[K] A) (μ : A →ₗ[K] T)
    (hcomplex : μ.comp δ = 0) : B →ₗ[K] LinearMap.ker μ :=
  δ.codRestrict (LinearMap.ker μ) fun b => by
    change μ (δ b) = 0
    have h := LinearMap.congr_fun hcomplex b
    simpa using h

abbrev FirstHomology (δ : B →ₗ[K] A) (μ : A →ₗ[K] T)
    (hcomplex : μ.comp δ = 0) :=
  (LinearMap.ker μ) ⧸ LinearMap.range (boundaryToCycles δ μ hcomplex)

/-- Euler characteristic of a three-term finite complex with injective first map. -/
theorem complex_euler (δ : B →ₗ[K] A) (μ : A →ₗ[K] T)
    (hcomplex : μ.comp δ = 0) (hδ : Function.Injective δ) :
    (finrank K (T ⧸ LinearMap.range μ) : ℤ) -
      finrank K (FirstHomology δ μ hcomplex) =
    (finrank K T : ℤ) - finrank K A + finrank K B := by
  have hδ' : Function.Injective (boundaryToCycles δ μ hcomplex) := by
    intro x y hxy
    exact hδ (congrArg Subtype.val hxy)
  have hb := LinearMap.finrank_range_of_inj hδ'
  have hh := (LinearMap.range (boundaryToCycles δ μ hcomplex)).finrank_quotient_add_finrank
  have hc := (LinearMap.range μ).finrank_quotient_add_finrank
  have hm := μ.finrank_range_add_finrank_ker
  rw [hb] at hh
  change finrank K (FirstHomology δ μ hcomplex) + finrank K B =
    finrank K (LinearMap.ker μ) at hh
  omega
end Complex

/-- Removing one more generator reduces the expected Euler characteristic by `N-r`. -/
theorem euler_succ_sub (n d r : ℕ) :
    euler n d (r + 1) - euler n d r = (r : ℤ) - (n + d - 1).choose d := by
  have hchoose : (r + 1).choose 2 = r.choose 2 + r := by
    rw [Nat.choose_succ_succ]
    simp [Nat.add_comm]
  simp only [euler, hchoose, Nat.cast_add, Nat.cast_one]
  ring

theorem euler_succ_lt (n d r : ℕ) (hr : r < (n + d - 1).choose d) :
    euler n d (r + 1) < euler n d r := by
  have he := euler_succ_sub n d r
  omega

/-- The dimension of an actual endpoint quotient decreases under extension. -/
theorem endpoint_quotient_antitone {K : Type*} [Field K] {n d : ℕ}
    {W W' : Submodule K (Poly K n)} (h : W ≤ W') :
    finrank K (EndpointQuotient K n d W') ≤ finrank K (EndpointQuotient K n d W) := by
  have hp := Submodule.finrank_mono (endpointProducts_mono (d := d) h)
  have hw := (endpointProducts K n d W).finrank_quotient_add_finrank
  have hw' := (endpointProducts K n d W').finrank_quotient_add_finrank
  change finrank K ((Forms K n (2 * d)) ⧸ endpointProducts K n d W') ≤
    finrank K ((Forms K n (2 * d)) ⧸ endpointProducts K n d W)
  omega

/-- Maximal rank is equivalent to one of the two nonnegative defects vanishing. -/
theorem maximal_rank_iff (H C : ℕ) (χ : ℤ) (hEuler : (C : ℤ) - H = χ) :
    (H = 0 ∨ C = 0) ↔ C = χ.toNat ∧ H = (-χ).toNat := by
  omega

/-- The numerical two-critical-count argument, including a coincident integral root.
No geometric monotonicity result is being assumed implicitly. -/
theorem all_counts_of_two_critical_zeros
    (H C : ℕ → ℕ) (χ : ℕ → ℤ) (D lower upper : ℕ)
    (hlower : lower ≤ D) (_hupper : upper ≤ D) (hgap : upper ≤ lower + 1)
    (hHmono : ∀ a b, a ≤ b → b ≤ D → H a ≤ H b)
    (hCanti : ∀ a b, a ≤ b → b ≤ D → C b ≤ C a)
    (hEuler : ∀ r ≤ D, (C r : ℤ) - H r = χ r)
    (hzero : max (H lower) (C upper) = 0) :
    ∀ r ≤ D, C r = (χ r).toNat ∧ H r = (-(χ r)).toNat := by
  have hzH : H lower = 0 := by omega
  have hzC : C upper = 0 := by omega
  intro r hr
  apply (maximal_rank_iff (H r) (C r) (χ r) (hEuler r hr)).mp
  by_cases hrl : r ≤ lower
  · left
    have hm := hHmono r lower hrl hlower
    omega
  · right
    have hur : upper ≤ r := by omega
    have hm := hCanti upper r hur hr
    omega

end Froberg
