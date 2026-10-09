module

public import Quartic.ConvolutionInitialSplit

@[expose] public section

/-! # The constant and variable slots in the ordered degree-one decomposition -/
noncomputable section
namespace Quartic.OrderedDegreeOne
open FreeCoefficients FreeMonomialCounts ConvolutionLayers ConvolutionInitialSplit
open OrderedFreeExponents

/-- Degree at most one has one constant monomial and one monomial per variable. -/
theorem card_bounded_one (w : ℕ) : Fintype.card (BoundedExponent w 1)=w+1 := by
  have h0 : Fintype.card (ExactExponent w 0)=1 :=
    Fintype.card_eq_one_iff.mpr ⟨zeroExponent w,exactExponent_zero_unique⟩
  have h1 : Fintype.card (ExactExponent w 1)=w := by
    rw [←Fintype.card_congr (oneExponentEquiv (w := w))]
    simp
  rw [Fintype.card_congr (exponentDegreeEquiv (w := w) (d := 1)),Fintype.card_sigma]
  change (∑ k : Fin 2,Fintype.card (ExactExponent w k.val))=w+1
  rw [Fin.sum_univ_two]
  change Fintype.card (ExactExponent w 0)+Fintype.card (ExactExponent w 1)=w+1
  rw [h0,h1]
  omega

/-- The increasing monomial enumeration with its explicit degree-one cardinality. -/
def enumeration (w : ℕ) : Fin (w+1) ≃ BoundedExponent w 1 :=
  (finCongr (card_bounded_one w).symm).trans (enumerate w 1)

theorem enumeration_lt_iff {w : ℕ} (i j : Fin (w+1)) :
    (monomialOrder w).toSyn (enumeration w i).val <
      (monomialOrder w).toSyn (enumeration w j).val ↔ i<j := by
  simpa only [enumeration,Equiv.trans_apply,finCongr_apply,Fin.cast_lt_cast] using
    (enumerate_lt_iff (Fin.cast (card_bounded_one w).symm i) (Fin.cast (card_bounded_one w).symm j))

/-- The constant is the first monomial in every monomial order. -/
theorem enumeration_zero (w : ℕ) : enumeration w 0=zeroBounded w := by
  let j := (enumeration w).symm (zeroBounded w)
  have hj : j=0 := by
    by_contra h
    have hpos : (0 : Fin (w+1))<j := Fin.pos_iff_ne_zero.mpr h
    have hlt := (enumeration_lt_iff 0 j).mpr hpos
    have he : enumeration w j=zeroBounded w := (enumeration w).apply_symm_apply _
    rw [he] at hlt
    change (monomialOrder w).toSyn (enumeration w 0).val < (monomialOrder w).toSyn 0 at hlt
    rw [(monomialOrder w).toSyn.map_zero] at hlt
    exact (not_lt_of_ge ((monomialOrder w).zero_le _)) hlt
  rw [←hj]
  exact (enumeration w).apply_symm_apply _

theorem enumeration_succ_degree {w : ℕ} (i : Fin w) :
    (enumeration w i.succ).val.degree=1 := by
  have h := (enumeration w i.succ).property
  have hn : (enumeration w i.succ).val.degree≠0 := by
    intro hz
    have he : enumeration w i.succ=enumeration w 0 := by
      rw [enumeration_zero]
      apply Subtype.ext
      exact (Finsupp.degree_eq_zero_iff _).mp hz
    have hi := (enumeration w).injective he
    exact Fin.succ_ne_zero i hi
  omega

/-- The remaining ordered slots are a permutation of the actual free variables. -/
def freePermutation (w : ℕ) : Fin w ≃ Fin w :=
  Equiv.ofBijective (fun i => oneExponentEquiv.symm
    ⟨(enumeration w i.succ).val,enumeration_succ_degree i⟩) (by
    constructor
    · intro i j h
      have hv := congrArg (fun k => (oneExponentEquiv k).val) h
      simp only [Equiv.apply_symm_apply] at hv
      exact Fin.succ_injective w ((enumeration w).injective (Subtype.ext hv))
    · intro k
      let j := (enumeration w).symm (oneBounded k)
      have hj : j≠0 := by
        intro h
        have hz := (enumeration w).apply_symm_apply (oneBounded k)
        rw [show (enumeration w).symm (oneBounded k)=0 from h,enumeration_zero] at hz
        have hv := congrArg (fun b : BoundedExponent w 1 => b.val.degree) hz
        have hdeg := (oneExponentEquiv k).property
        change (0 : Fin w →₀ ℕ).degree=(oneExponentEquiv k).val.degree at hv
        simp only [map_zero,hdeg] at hv
        omega
      obtain ⟨i,hi⟩ := Fin.exists_succ_eq.mpr hj
      refine ⟨i,?_⟩
      apply oneExponentEquiv.injective
      apply Subtype.ext
      simp only [Equiv.apply_symm_apply]
      have he : enumeration w i.succ=oneBounded k := by
        rw [hi]
        exact (enumeration w).apply_symm_apply _
      exact congrArg Subtype.val he)

theorem enumeration_succ {w : ℕ} (i : Fin w) :
    enumeration w i.succ=oneBounded (freePermutation w i) := by
  apply Subtype.ext
  change _=(oneExponentEquiv (oneExponentEquiv.symm _)).val
  simp only [Equiv.apply_symm_apply]

end Quartic.OrderedDegreeOne
