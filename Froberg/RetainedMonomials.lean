import Froberg.InitialSubspace

/-! Coordinate projections retaining any chosen monomials, and the initial
subspace argument after such a projection. This includes deleting a bidegree. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
open scoped MonomialOrder Classical

variable {K σ : Type*} [Field K]

def retainMonomials (P : (σ →₀ ℕ) → Prop) :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K := by
  classical
  let F : ((σ →₀ ℕ) →₀ K) →ₗ[K] ((σ →₀ ℕ) →₀ K) :=
    { toFun := Finsupp.filter P
      map_add' := by intros; exact Finsupp.filter_add
      map_smul' := by intros; exact Finsupp.filter_smul }
  exact (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    (F.comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

theorem coeff_retainMonomials (P : (σ →₀ ℕ) → Prop)
    (f : MvPolynomial σ K) (a : σ →₀ ℕ) :
    (retainMonomials P f).coeff a = if P a then f.coeff a else 0 := by
  classical
  rfl

theorem retainMonomials_ne_zero (m : MonomialOrder σ) (P : (σ →₀ ℕ) → Prop)
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hP : P (m.degree f)) :
    retainMonomials P f ≠ 0 := by
  intro h
  have hc := congrArg (fun p : MvPolynomial σ K => p.coeff (m.degree f)) h
  rw [coeff_retainMonomials, ite_eq_left hP] at hc
  exact (m.coeff_degree_ne_zero_iff.mpr hf) hc

theorem degree_retainMonomials (m : MonomialOrder σ) (P : (σ →₀ ℕ) → Prop)
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hP : P (m.degree f)) :
    m.degree (retainMonomials P f) = m.degree f := by
  classical
  apply m.toSyn.injective
  apply le_antisymm
  · apply m.degree_le_degree_of_support_subset
    intro a ha
    have hc : (retainMonomials P f).coeff a ≠ 0 := mem_support_iff.mp ha
    rw [coeff_retainMonomials] at hc
    split_ifs at hc with hpa
    · exact mem_support_iff.mpr hc
    · exact False.elim (hc rfl)
  · apply m.le_degree
    apply mem_support_iff.mpr
    rw [coeff_retainMonomials, ite_eq_left hP]
    exact m.coeff_degree_ne_zero_iff.mpr hf

variable {n d e : ℕ}

/-- The shadow bound survives deleting arbitrary target coordinates, provided
the counted leading monomials are retained. -/
theorem card_le_finrank_retained_product_of_initial_factors
    (m : MonomialOrder (Fin n)) (P : (Fin n →₀ ℕ) → Prop)
    (U : Submodule K (Poly K n)) (hU : U ≤ Forms K n e)
    (B : Finset (Fin n →₀ ℕ)) (hP : ∀ b ∈ B, P b)
    (hB : ∀ b ∈ B, ∃ a ∈ initialDegrees (d := e) m U,
      ∃ c : Fin n →₀ ℕ, c.degree = d ∧ a + c = b) :
    B.card ≤ finrank K ((U * Forms K n d).map (retainMonomials P)) := by
  classical
  have hfinite : U * Forms K n d ≤ Forms K n (e + d) :=
    (mul_le_mul_left hU _).trans (MvPolynomial.homogeneousSubmodule_mul e d)
  let : FiniteDimensional K (U * Forms K n d) :=
    Submodule.finiteDimensional_of_le hfinite
  have hex (b : B) : ∃ g : (U * Forms K n d).map (retainMonomials P),
      g.val ≠ 0 ∧ m.degree g.val = b.val := by
    obtain ⟨a, ha, c, hc, hab⟩ := hB b.val b.property
    obtain ⟨f, hf, hfn, hfa⟩ := (mem_initialDegrees m U hU a).mp ha
    have hmon : (monomial c (1 : K) : Poly K n) ≠ 0 := by simp
    let g := f * monomial c (1 : K)
    have hgn : g ≠ 0 := mul_ne_zero hfn hmon
    have hgd : m.degree g = b.val := by
      rw [m.degree_mul hfn hmon, hfa, m.degree_monomial, ite_eq_right one_ne_zero]
      exact hab
    have hgP : P (m.degree g) := by rw [hgd]; exact hP b.val b.property
    refine ⟨⟨retainMonomials P g, ?_⟩,
      retainMonomials_ne_zero m P g hgn hgP, ?_⟩
    · exact ⟨g, Submodule.mul_mem_mul hf (isHomogeneous_monomial 1 hc), rfl⟩
    · exact (degree_retainMonomials m P g hgn hgP).trans hgd
  choose g hgn hgd using hex
  have hli : LinearIndependent K (fun b : B => (g b).val) :=
    linearIndependent_of_distinct_leading m _ hgn (by
      intro a b hab
      apply Subtype.ext
      simpa only [hgd] using hab)
  simpa using (LinearIndependent.of_comp
    ((U * Forms K n d).map (retainMonomials P)).subtype hli).fintype_card_le_finrank

end Froberg
