import Quartic.Homogeneous

/-!
# Polarization and a surviving quadratic square

The marked-generator argument in `transfer.tex` uses the fact that a nonzero
quartic quotient cannot kill the squares of every quadratic polynomial. This
file proves that assertion for the actual homogeneous polynomial spaces.
-/

namespace Quartic.Squares

noncomputable section

section Polarization

variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

/-- If a submodule contains every square of a vector in `V`, it contains every
product of two vectors in `V`. The polarization is valid because two is
invertible in the coefficient field. -/
theorem products_le_of_squares (V I : Submodule K A)
    (hsq : ∀ x ∈ V, x ^ 2 ∈ I) : V * V ≤ I := by
  apply Submodule.mul_le.mpr
  intro x hx y hy
  have hsum := hsq (x + y) (V.add_mem hx hy)
  have hdiff : (x + y) ^ 2 - x ^ 2 - y ^ 2 ∈ I :=
    I.sub_mem (I.sub_mem hsum (hsq x hx)) (hsq y hy)
  have hpolar : (x + y) ^ 2 - x ^ 2 - y ^ 2 = (2 : K) • (x * y) := by
    simp only [two_smul]
    ring
  rw [hpolar] at hdiff
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hhalf := I.smul_mem ((2 : K)⁻¹) hdiff
  simpa only [smul_smul, inv_mul_cancel₀ htwo, one_smul] using hhalf

/-- If the product space survives a quotient, some square already survives. -/
theorem exists_square_not_mem (V I : Submodule K A) (h : ¬ V * V ≤ I) :
    ∃ x ∈ V, x ^ 2 ∉ I := by
  by_contra hn
  push Not at hn
  exact h (products_le_of_squares V I hn)

include K

/-- Elementary zero-product version of polarization. -/
theorem mul_eq_zero_of_squares_eq_zero (hsq : ∀ x : A, x ^ 2 = 0)
    (x y : A) : x * y = 0 := by
  have h : (⊤ : Submodule K A) * ⊤ ≤ ⊥ :=
    products_le_of_squares ⊤ ⊥ (by simpa using hsq)
  exact h (Submodule.mul_mem_mul (Submodule.mem_top) (Submodule.mem_top))

end Polarization

section Homogeneous

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Killing every quadratic square kills all quartics, since products of
quadratics span the actual homogeneous quartic space. -/
theorem quartics_le_of_quadratic_squares (I : Submodule K (Quartic.Poly K n))
    (hsq : ∀ f ∈ Quartic.Forms K n 2, f ^ 2 ∈ I) :
    Quartic.Forms K n 4 ≤ I := by
  rw [← Quartic.quadrics_mul_quadrics]
  exact products_le_of_squares _ I hsq

/-- The same statement for an ideal of the polynomial algebra. -/
theorem quartics_mem_ideal_of_quadratic_squares (I : Ideal (Quartic.Poly K n))
    (hsq : ∀ f ∈ Quartic.Forms K n 2, f ^ 2 ∈ I) :
    ∀ g ∈ Quartic.Forms K n 4, g ∈ I :=
  quartics_le_of_quadratic_squares (I.restrictScalars K) hsq

/-- A quartic quotient that has not vanished admits a quadratic whose square
does not vanish in the quotient. This is the existence part of the marked
coefficient argument. -/
theorem exists_quadratic_with_square_not_mem
    (I : Submodule K (Quartic.Poly K n)) (h : ¬ Quartic.Forms K n 4 ≤ I) :
    ∃ f : Quartic.Forms K n 2, (f : Quartic.Poly K n) ^ 2 ∉ I := by
  have hprod : ¬ Quartic.Forms K n 2 * Quartic.Forms K n 2 ≤ I := by
    rwa [Quartic.quadrics_mul_quadrics]
  obtain ⟨f, hf, hnot⟩ := exists_square_not_mem _ I hprod
  exact ⟨⟨f, hf⟩, hnot⟩

/-- A square survives whenever the actual degree-four multiplication image
is proper. This applies directly to the lower child endpoint of the transfer. -/
theorem exists_square_outside_quarticProducts
    (Q : Submodule K (Quartic.Poly K n))
    (hQ : Quartic.quarticProducts K n Q ≠ ⊤) :
    ∃ f : Quartic.Forms K n 2,
      Quartic.mulQuadratic f f ∉ Quartic.quarticProducts K n Q := by
  have hproper : ¬ Quartic.Forms K n 4 ≤ Q * Quartic.Forms K n 2 := by
    intro h
    apply hQ
    apply top_unique
    intro g _
    exact h g.property
  obtain ⟨f, hf⟩ := exists_quadratic_with_square_not_mem
    (Q * Quartic.Forms K n 2) hproper
  refine ⟨f, ?_⟩
  change (f : Quartic.Poly K n) * (f : Quartic.Poly K n) ∉ Q * Quartic.Forms K n 2
  simpa only [pow_two] using hf

end Homogeneous

end

end Quartic.Squares
