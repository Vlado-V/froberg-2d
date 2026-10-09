module

public import Froberg.Graded
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

@[expose] public section

/-! Initial monomials of finite homogeneous subspaces. These are extracted
from the actual polynomial subspace, with their cardinality proved by linear algebra. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
open scoped MonomialOrder

variable {K σ ι : Type*} [Field K]

/-- Distinct leading exponents make a finite family of nonzero polynomials
linearly independent. The proof inspects the largest active exponent. -/
theorem linearIndependent_of_distinct_leading [Fintype ι]
    (m : MonomialOrder σ) (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) (hinj : Function.Injective (fun i => m.degree (f i))) :
    LinearIndependent K f := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  by_contra hzero
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hzero h
  let s : Finset ι := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => m.toSyn (m.degree (f j))) hs
  have hci : c i ≠ 0 := (Finset.mem_filter.mp hi).2
  have hcoeff : ∀ j ∈ Finset.univ, j ≠ i →
      c j • (f j).coeff (m.degree (f i)) = 0 := by
    intro j _ hji
    by_cases hcj : c j = 0
    · simp [hcj]
    · have hj : j ∈ s := by simp [s, hcj]
      have hlt : m.degree (f j) ≺[m] m.degree (f i) := by
        apply lt_of_le_of_ne (hmax j hj)
        intro he
        exact hji (hinj (m.toSyn.injective he))
      rw [m.coeff_eq_zero_of_lt hlt, smul_zero]
  have hh := congrArg (lcoeff K (m.degree (f i))) hc
  simp only [map_sum, map_smul, map_zero] at hh
  change (∑ j, c j • (f j).coeff (m.degree (f i))) = 0 at hh
  rw [Finset.sum_eq_single i hcoeff (by simp)] at hh
  exact (mul_ne_zero hci (m.coeff_degree_ne_zero_iff.mpr (hf i))) hh

variable {n d : ℕ}

/-- The finite set of leading exponents realized by a homogeneous subspace. -/
def initialDegrees (m : MonomialOrder (Fin n)) (U : Submodule K (Poly K n)) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (Finset.univ.image (fun s : Sym (Fin n) d => (exponentEquiv n d s).val)).filter
    (fun a => ∃ f ∈ U, f ≠ 0 ∧ m.degree f = a)

theorem mem_initialDegrees (m : MonomialOrder (Fin n)) (U : Submodule K (Poly K n))
    (hU : U ≤ Forms K n d) (a : Fin n →₀ ℕ) :
    a ∈ initialDegrees (d := d) m U ↔ ∃ f ∈ U, f ≠ 0 ∧ m.degree f = a := by
  classical
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).2
  · rintro ⟨f, hf, hn, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ⟨f, hf, hn, rfl⟩⟩
    have hdeg : (m.degree f).degree = d := by
      have hd := (hU hf).degree_eq_sum_deg_support (m.degree_mem_support hn)
      exact hd.symm
    refine Finset.mem_image.mpr ⟨(exponentEquiv n d).symm ⟨m.degree f, hdeg⟩,
      Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((exponentEquiv n d).apply_symm_apply _)

theorem initialDegrees_degree (m : MonomialOrder (Fin n)) (U : Submodule K (Poly K n))
    {a : Fin n →₀ ℕ} (ha : a ∈ initialDegrees (d := d) m U) : a.degree = d := by
  classical
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).1
  exact (exponentEquiv n d s).property

/-- Initial monomials have exactly the dimension of the original subspace. -/
theorem card_initialDegrees (m : MonomialOrder (Fin n)) (U : Submodule K (Poly K n))
    (hU : U ≤ Forms K n d) :
    (initialDegrees (d := d) m U).card = finrank K U := by
  classical
  let : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  let A := initialDegrees (d := d) m U
  have hex (a : A) : ∃ f : U, f.val ≠ 0 ∧ m.degree f.val = a.val := by
    obtain ⟨f, hf, hn, hd⟩ := (mem_initialDegrees m U hU a.val).mp a.property
    exact ⟨⟨f, hf⟩, hn, hd⟩
  choose f hf hd using hex
  have hli : LinearIndependent K (fun a : A => (f a).val) :=
    linearIndependent_of_distinct_leading m _ hf (by
      intro a b hab
      apply Subtype.ext
      simpa only [hd] using hab)
  have hlow : A.card ≤ finrank K U := by
    simpa using (LinearIndependent.of_comp U.subtype hli).fintype_card_le_finrank
  let coord : U →ₗ[K] (A → K) := LinearMap.pi (fun a => (lcoeff K a.val).comp U.subtype)
  have hcoord : Function.Injective coord := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    by_contra hn
    have hxn : x.val ≠ 0 := by simpa only [Subtype.ext_iff, Submodule.coe_zero] using hn
    have ha : m.degree x.val ∈ A := (mem_initialDegrees m U hU _).mpr
      ⟨x.val, x.property, hxn, rfl⟩
    have hc := congrFun hx (⟨m.degree x.val, ha⟩ : A)
    exact (m.coeff_degree_ne_zero_iff.mpr hxn) hc
  have hupp := LinearMap.finrank_le_finrank_of_injective hcoord
  have hupp' : finrank K U ≤ A.card := by simpa using hupp
  exact le_antisymm hlow hupp'

/-- Any distinct monomial multiples of the initial exponents give independent
actual products. This is the initial-subspace transfer needed for shadow bounds. -/
theorem card_le_finrank_product_of_initial_factors {e : ℕ}
    (m : MonomialOrder (Fin n)) (U : Submodule K (Poly K n))
    (hU : U ≤ Forms K n e) (B : Finset (Fin n →₀ ℕ))
    (hB : ∀ b ∈ B, ∃ a ∈ initialDegrees (d := e) m U,
      ∃ c : Fin n →₀ ℕ, c.degree = d ∧ a + c = b) :
    B.card ≤ finrank K (U * Forms K n d) := by
  classical
  have hfinite : U * Forms K n d ≤ Forms K n (e + d) :=
    (mul_le_mul_left hU _).trans (MvPolynomial.homogeneousSubmodule_mul e d)
  let : FiniteDimensional K (U * Forms K n d) :=
    Submodule.finiteDimensional_of_le hfinite
  have hex (b : B) : ∃ g : U * Forms K n d,
      g.val ≠ 0 ∧ m.degree g.val = b.val := by
    obtain ⟨a, ha, c, hc, hab⟩ := hB b.val b.property
    obtain ⟨f, hf, hfn, hfa⟩ := (mem_initialDegrees m U hU a).mp ha
    have hmon : (monomial c (1 : K) : Poly K n) ≠ 0 := by simp
    refine ⟨⟨f * monomial c 1, Submodule.mul_mem_mul hf
      (isHomogeneous_monomial 1 hc)⟩, mul_ne_zero hfn hmon, ?_⟩
    rw [m.degree_mul hfn hmon, hfa, m.degree_monomial, ite_eq_right one_ne_zero]
    exact hab
  choose g hgn hgd using hex
  have hli : LinearIndependent K (fun b : B => (g b).val) :=
    linearIndependent_of_distinct_leading m _ hgn (by
      intro a b hab
      apply Subtype.ext
      simpa only [hgd] using hab)
  simpa using (LinearIndependent.of_comp (U * Forms K n d).subtype hli).fintype_card_le_finrank

end Froberg
