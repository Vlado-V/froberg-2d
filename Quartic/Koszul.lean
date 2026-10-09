module

public import Quartic.Homogeneous
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Fintype.Prod

@[expose] public section

noncomputable section

namespace Quartic

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}

abbrev GeneratorPair (r : ℕ) := {p : Fin r × Fin r // p.1 < p.2}

theorem card_generatorPair : Fintype.card (GeneratorPair r) = r.choose 2 := by
  simpa [GeneratorPair, Fintype.card_subtype] using
    (Fintype.card_product_filter_lt (α := Fin r))

/-- Independent vectors admit simultaneous coordinate functionals. -/
theorem exists_coordinate_functionals (q : Fin r → V) (hq : LinearIndependent K q) :
    ∃ dual : Fin r → V →ₗ[K] K, ∀ i j, dual i (q j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination K q).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hq)
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  intro i j
  have h := LinearMap.congr_fun hg (Finsupp.single j 1)
  have hj : g (q j) = Finsupp.single j 1 := by simpa using h
  simp [hj, Finsupp.single_apply, eq_comm]

/-- A constant incoming Koszul relation on a pair of generators. -/
def koszulVector (q : Fin r → V) (p : GeneratorPair r) : Fin r → V :=
  fun i => (if i = p.val.1 then q p.val.2 else 0) -
    (if i = p.val.2 then q p.val.1 else 0)

set_option maxRecDepth 2048 in
theorem koszulVector_coordinate (q : Fin r → V)
    (dual : Fin r → V →ₗ[K] K)
    (hdual : ∀ i j, dual i (q j) = if i = j then 1 else 0)
    (p t : GeneratorPair r) :
    dual p.val.2 (koszulVector q t p.val.1) = if p = t then 1 else 0 := by
  classical
  simp only [koszulVector, map_sub, apply_ite, map_zero, hdual]
  have hp := p.property
  have ht := t.property
  by_cases heq : p = t
  · subst t
    simp [ne_of_lt hp]
  · have hneq : ¬(p.val.1 = t.val.1 ∧ p.val.2 = t.val.2) := by
      intro h
      exact heq (Subtype.ext (Prod.ext h.1 h.2))
    simp only [heq, ite_false]
    split_ifs <;> simp_all
    all_goals omega

/-- The forced pairwise relations are independent whenever the quadrics are. -/
theorem koszulVector_linearIndependent (q : Fin r → V) (hq : LinearIndependent K q) :
    LinearIndependent K (koszulVector q) := by
  classical
  obtain ⟨dual, hdual⟩ := exists_coordinate_functionals q hq
  apply Fintype.linearIndependent_iff.mpr
  intro a ha p
  have h := congrArg (fun z : Fin r → V => dual p.val.2 (z p.val.1)) ha
  simpa only [Finset.sum_apply, map_sum, Pi.smul_apply, map_smul,
    koszulVector_coordinate q dual hdual, Pi.zero_apply, map_zero,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    Finset.sum_ite_eq, ite_true] using h

variable {n : ℕ}

/-- Multiplication for an ordered family of quadrics. -/
def quadraticMultiplication (q : Fin r → Forms K n 2) :
    (Fin r → Forms K n 2) →ₗ[K] Forms K n 4 :=
  ∑ i, (mulQuadratic (q i)).comp (LinearMap.proj i)

theorem quadraticMultiplication_koszul (q : Fin r → Forms K n 2) (p : GeneratorPair r) :
    quadraticMultiplication q (koszulVector q p) = 0 := by
  classical
  apply Subtype.ext
  simp only [quadraticMultiplication, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.coe_sum]
  change (∑ i, (q i).val * (koszulVector q p i).val) = 0
  have hcoe (i j : Fin r) (a : Forms K n 2) :
      ((if i = j then a else 0) : Forms K n 2).val = if i = j then a.val else 0 := by
    split_ifs <;> rfl
  simp only [koszulVector, Submodule.coe_sub, hcoe,
    mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sub_eq_zero.mpr (mul_comm (q p.val.1).val (q p.val.2).val)

theorem kernel_contains_koszul (q : Fin r → Forms K n 2) :
    Submodule.span K (Set.range (koszulVector q)) ≤ LinearMap.ker (quadraticMultiplication q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact quadraticMultiplication_koszul q p

/-- The kernel has at least one independent commutativity relation per generator pair. -/
theorem koszul_kernel_lower_bound (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    r.choose 2 ≤ finrank K (LinearMap.ker (quadraticMultiplication q)) := by
  have h := Submodule.finrank_mono (kernel_contains_koszul q)
  rw [finrank_span_eq_card (koszulVector_linearIndependent q hq), card_generatorPair] at h
  exact h

/-- Universal degree-four rank bound including the full Koszul correction. -/
theorem quartic_rank_add_pairs_le (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (LinearMap.range (quadraticMultiplication q)) + r.choose 2 ≤
      r * (n + 1).choose 2 := by
  have h := (quadraticMultiplication q).finrank_range_add_finrank_ker
  have hk := koszul_kernel_lower_bound q hq
  have hdim : finrank K (Fin r → Forms K n 2) = r * (n + 1).choose 2 := by
    simp [Module.finrank_pi_fintype, finrank_quadrics]
  rw [hdim] at h
  exact (Nat.add_le_add_left hk _).trans_eq h

end Quartic
