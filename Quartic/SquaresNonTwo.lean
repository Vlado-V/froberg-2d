module

public import Quartic.Squares

@[expose] public section

/-! Polarization needs only nonvanishing of two, not characteristic zero. -/
noncomputable section
namespace Quartic.SquaresNonTwo
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem products_le_of_squares (h2 : (2 : K) ≠ 0) (V I : Submodule K A)
    (hsq : ∀ x ∈ V, x^2 ∈ I) : V*V ≤ I := by
  apply Submodule.mul_le.mpr
  intro x hx y hy
  have hdiff : (x+y)^2-x^2-y^2 ∈ I :=
    I.sub_mem (I.sub_mem (hsq (x+y) (V.add_mem hx hy)) (hsq x hx)) (hsq y hy)
  have he : (x+y)^2-x^2-y^2 = (2 : K) • (x*y) := by
    simp only [two_smul]
    ring
  rw [he] at hdiff
  simpa only [smul_smul,inv_mul_cancel₀ h2,one_smul] using I.smul_mem (2 : K)⁻¹ hdiff

theorem exists_square_outside (h2 : (2 : K) ≠ 0) {n : ℕ}
    (Q : Submodule K (Poly K n)) (hQ : quarticProducts K n Q ≠ ⊤) :
    ∃ v : Forms K n 2, mulQuadratic v v ∉ quarticProducts K n Q := by
  by_contra! h
  apply hQ
  apply top_unique
  have hsq : ∀ x ∈ Forms K n 2, x^2 ∈ Q * Forms K n 2 := by
    intro x hx
    have hh := h ⟨x,hx⟩
    change x*x ∈ Q*Forms K n 2 at hh
    simpa only [pow_two] using hh
  have he := products_le_of_squares h2 (Forms K n 2) (Q*Forms K n 2) hsq
  rw [quadrics_mul_quadrics] at he
  intro z _
  exact he z.property

end Quartic.SquaresNonTwo
