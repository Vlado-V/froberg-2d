import Quartic.EndpointHomology
import Quartic.RankOpen

/-!
# Reduction to adjacent endpoint witnesses

The two witness conditions concern the actual multiplication complex:
all kernel elements are Koszul boundaries, or multiplication is surjective.
The first passes to smaller independent families; the second passes to larger
independent families up to the dimension of the quadratic space. Together with
the Euler identity and the determinant-open theorem, this proves the actual
generic assertion at every generator count from two adjacent endpoint witnesses.
-/

namespace Quartic.EndpointReduction

noncomputable section

open Module Quartic.EndpointHomology

variable {K : Type*} [Field K] {n r : ℕ}

/-- Existence of an independent family with no relations beyond Koszul ones. -/
def NoHomologyWitness (K : Type*) [Field K] (n r : ℕ) : Prop :=
  ∃ q : Fin r → Forms K n 2, LinearIndependent K q ∧
    LinearMap.ker (quadraticMultiplication q) ≤ koszulSpace q

/-- Existence of an independent family spanning all quartics by multiplication. -/
def SurjectiveWitness (K : Type*) [Field K] (n r : ℕ) : Prop :=
  ∃ q : Fin r → Forms K n 2, LinearIndependent K q ∧
    Function.Surjective (quadraticMultiplication q)

theorem noHomology_delete_last (h : NoHomologyWitness K n (r + 1)) :
    NoHomologyWitness K n r := by
  obtain ⟨q, hq, hexact⟩ := h
  refine ⟨prefixFamily q, hq.comp _ (Fin.castSucc_injective r), ?_⟩
  intro a ha
  have hcycle : extendZero (K := K) a ∈ LinearMap.ker (quadraticMultiplication q) := by
    change quadraticMultiplication q (extendZero a) = 0
    rw [quadraticMultiplication_extendZero]
    exact ha
  exact (extendZero_mem_boundarySpan_iff q hq a).mp (hexact hcycle)

theorem noHomology_downward {s : ℕ} (h : NoHomologyWitness K n s) (hrs : r ≤ s) :
    NoHomologyWitness K n r := by
  induction s generalizing r with
  | zero =>
    have hr : r = 0 := by omega
    subst r
    exact h
  | succ s ih =>
    by_cases heq : r = s + 1
    · subst r; exact h
    · exact ih (noHomology_delete_last h) (by omega)

theorem surjective_adjoin_one (h : SurjectiveWitness K n r)
    (hr : r < (n + 1).choose 2) : SurjectiveWitness K n (r + 1) := by
  obtain ⟨q, hq, hsurj⟩ := h
  obtain ⟨f, hf⟩ := exists_linearIndependent_snoc_of_lt_finrank hq
    (by simpa [finrank_quadrics] using hr)
  refine ⟨Fin.snoc q f, hf, ?_⟩
  intro g
  obtain ⟨a, ha⟩ := hsurj g
  refine ⟨extendZero (K := K) a, ?_⟩
  rw [quadraticMultiplication_extendZero]
  have hp : prefixFamily (Fin.snoc q f) = q := by
    funext i
    simp [prefixFamily]
  rw [hp]
  exact ha

theorem surjective_upward {s : ℕ} (h : SurjectiveWitness K n s)
    (hsr : s ≤ r) (hr : r ≤ (n + 1).choose 2) : SurjectiveWitness K n r := by
  induction r generalizing s with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact h
  | succ r ih =>
    by_cases heq : s = r + 1
    · subst s; exact h
    · exact surjective_adjoin_one (ih h (by omega) (by omega)) (by omega)

/-- Convert an ordered witness into the intrinsic subspace witness. -/
theorem witness_of_ordered (q : Fin r → Forms K n 2) (hq : LinearIndependent K q)
    (hdim : finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val)))) = expectedDimension n r) :
    QuarticWitness K n r := by
  refine ⟨Submodule.span K (Set.range (fun i => (q i).val)), ?_, ?_, hdim⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (q i).property
  · have hi := hq.map' (Forms K n 2).subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
    change LinearIndependent K (fun i => (q i).val) at hi
    rw [finrank_span_eq_card hi, Fintype.card_fin]

theorem noHomology_implies_witness (h : NoHomologyWitness K n r) :
    QuarticWitness K n r := by
  obtain ⟨q, hq, hexact⟩ := h
  apply witness_of_ordered q hq
  apply (expected_quotient_iff_homology_or_quotient_zero q hq).mpr
  left
  have heq : koszulSpace q = LinearMap.ker (quadraticMultiplication q) :=
    le_antisymm (kernel_contains_koszul q) hexact
  have hdim : finrank K (LinearMap.ker (quadraticMultiplication q)) = r.choose 2 := by
    rw [← heq]
    exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  have hhom := homology_add_pairs q hq
  omega

theorem surjective_implies_witness (h : SurjectiveWitness K n r) :
    QuarticWitness K n r := by
  obtain ⟨q, hq, hsurj⟩ := h
  apply witness_of_ordered q hq
  apply (expected_quotient_iff_homology_or_quotient_zero q hq).mpr
  right
  have h := quartic_quotient_add_rank q
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_quartics] at h
  omega

/-- At a nonnegative Euler count, an expected-dimension witness has no
homology. This is an exact statement about the concrete multiplication kernel. -/
theorem noHomology_of_witness (h : QuarticWitness K n r) (hchi : 0 ≤ Counts.chi n r) :
    NoHomologyWitness K n r := by
  obtain ⟨Q, hQ, hQr, hdim⟩ := h
  obtain ⟨q, hq, hspan⟩ := quadratic_subspace_has_basis Q hQ
  subst r
  refine ⟨q, hq, ?_⟩
  have heuler := quartic_euler_identity q hq
  rw [hspan, hdim] at heuler
  change ((Counts.chi n (finrank K Q)).toNat : ℤ) - _ = _ at heuler
  have hhom := homology_add_pairs q hq
  have hB : finrank K (koszulSpace q) = (finrank K Q).choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  have heq : koszulSpace q = LinearMap.ker (quadraticMultiplication q) := by
    apply Submodule.eq_of_le_of_finrank_eq
      (show koszulSpace q ≤ LinearMap.ker (quadraticMultiplication q) from kernel_contains_koszul q)
    omega
  exact heq.ge

/-- At a nonpositive Euler count, an expected-dimension witness is surjective. -/
theorem surjective_of_witness (h : QuarticWitness K n r) (hchi : Counts.chi n r ≤ 0) :
    SurjectiveWitness K n r := by
  obtain ⟨Q, hQ, hQr, hdim⟩ := h
  obtain ⟨q, hq, hspan⟩ := quadratic_subspace_has_basis Q hQ
  subst r
  refine ⟨q, hq, LinearMap.range_eq_top.mp ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hcoker := quartic_quotient_add_rank q
  rw [hspan, hdim] at hcoker
  change (Counts.chi n (finrank K Q)).toNat + _ = _ at hcoker
  rw [Int.toNat_of_nonpos hchi] at hcoker
  simpa [finrank_quartics] using hcoker

/-- Two adjacent witnesses prove the generic quartic assertion at every
admissible generator count. The endpoint signs include a shared integral root. -/
theorem adjacent_endpoints_imply_generic (lo hi : ℕ)
    (hadjacent : hi ≤ lo + 1)
    (hlow : QuarticWitness K n lo) (hhigh : QuarticWitness K n hi)
    (hchi_low : 0 ≤ Counts.chi n lo) (hchi_high : Counts.chi n hi ≤ 0)
    (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r := by
  by_cases hrlow : r ≤ lo
  · exact witness_implies_generic
      (noHomology_implies_witness (noHomology_downward (noHomology_of_witness hlow hchi_low) hrlow))
  · exact witness_implies_generic
      (surjective_implies_witness (surjective_upward
        (surjective_of_witness hhigh hchi_high) (by omega) hr))

/-- The same endpoint reduction stated entirely in terms of the precise
principal-open generic assertion used by the formalization. -/
theorem adjacent_generic_endpoints_imply_generic (lo hi : ℕ)
    (hadjacent : hi ≤ lo + 1)
    (hlow : GenericQuartic K n lo) (hhigh : GenericQuartic K n hi)
    (hchi_low : 0 ≤ Counts.chi n lo) (hchi_high : Counts.chi n hi ≤ 0)
    (hr : r ≤ (n + 1).choose 2) : GenericQuartic K n r :=
  adjacent_endpoints_imply_generic lo hi hadjacent
    (genericQuartic_iff_witness.mp hlow) (genericQuartic_iff_witness.mp hhigh)
    hchi_low hchi_high hr

end

end Quartic.EndpointReduction
