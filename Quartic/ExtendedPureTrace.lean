/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.AugmentedMiddleOmega

/-!
# Four pure trace directions

The three ordinary pure homology directions and the fourth coefficient of
the exceptional square correction have independent scalar contractions.
This file proves the corresponding augmented injection and constructs its
motions from a codimension bound, over every field.
-/

@[expose] public section

noncomputable section
namespace Quartic.ExtendedPureTrace
open Module HomologyCoordinates AugmentedMiddle

variable {K : Type*} [Field K]
variable {V A : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A]

/-- Coefficients of the four traces after contracting along `(ω,-1)`. -/
def scalarCoefficients (ω : K) (t : Fin 4 → K) : Fin 4 → K :=
  ![-(1 + ω) * t 0, ω * t 1, t 2, (ω * (ω + 1)) * t 3]

theorem scalarCoefficients_eq_zero (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (t : Fin 4 → K) (ht : scalarCoefficients ω t = 0) : t = 0 := by
  have hsum : 1 + ω ≠ 0 := by
    intro h
    exact hω1 (eq_neg_of_add_eq_zero_right h)
  have hsum' : ω + 1 ≠ 0 := by simpa only [add_comm] using hsum
  have h0 := congrFun ht 0
  have h1 := congrFun ht 1
  have h2 := congrFun ht 2
  have h3 := congrFun ht 3
  simp only [scalarCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Pi.zero_apply] at h0 h1 h2 h3
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr hsum)
  · exact (mul_eq_zero.mp h1).resolve_left hω
  · exact h2
  · exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hω hsum')

/-- Ordinary trace coordinates followed by the exceptional square coefficient. -/
def trace (ω : K) (r : Fin 4 → A) : (Fin 4 → K) →ₗ[K] A × A where
  toFun t := (-t 0 • r 0 + t 2 • r 2 + (ω ^ 2 * t 3) • r 3,
    -t 0 • r 0 + t 1 • r 1 + t 3 • r 3)
  map_add' t u := by
    apply Prod.ext <;> simp only [Pi.add_apply, neg_add, mul_add, add_smul,
      Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' a t := by
    apply Prod.ext <;> simp only [Pi.smul_apply, smul_eq_mul, smul_add,
      smul_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply] <;> module

theorem trace_contract (ω : K) (r : Fin 4 → A) (t : Fin 4 → K) :
    (trace ω r t).1 + ω • (trace ω r t).2 =
      ∑ i, scalarCoefficients ω t i • r i := by
  simp [trace, scalarCoefficients, Fin.sum_univ_succ, smul_add, smul_smul]
  module

/-- The old three-dimensional trace is the subspace with last coordinate zero. -/
theorem trace_ordinary (ω : K) (r : Fin 4 → A) (t : Fin 3 → K) :
    trace ω r ![t 0, t 1, t 2, 0] = pureTrace r (homologyEquiv t) := by
  apply Prod.ext <;>
    simp [trace, pureTrace, homologyReduction_cycleClasses, homologyEquiv,
      ThreeBlock.coefficientMaps, Fin.sum_univ_succ]

/-- The extra trace is precisely the reduced fourth square-correction coefficient. -/
theorem trace_exceptional (ω : K) (r : Fin 4 → A) (a : K) :
    trace ω r ![0, 0, 0, a] = ((ω ^ 2 * a) • r 3, a • r 3) := by
  simp [trace]

def augmented (ω : K) (F : V →ₗ[K] A × A) (r : Fin 4 → A) :
    (V × (A × (Fin 4 → K))) →ₗ[K] A × A :=
  F.coprod (((ω • LinearMap.id : A →ₗ[K] A).prod (-LinearMap.id)).coprod (trace ω r))

@[simp] theorem augmented_apply (ω : K) (F : V →ₗ[K] A × A) (r : Fin 4 → A)
    (b : V) (a : A) (t : Fin 4 → K) :
    augmented ω F r (b, a, t) =
      ((F b).1 + ω • a + (trace ω r t).1,
        (F b).2 - a + (trace ω r t).2) := by
  apply Prod.ext <;> simp [augmented, sub_eq_add_neg, add_assoc]

/-- Four independent quotient motions separate products, marked terms, and all traces. -/
theorem augmented_injective (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (f : V →ₗ[K] A) (hf : Function.Injective f) (r : Fin 4 → A)
    (hr : LinearIndependent K (fun i => f.range.mkQ (r i))) :
    Function.Injective (augmented ω (f.prod 0) r) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  rintro ⟨b, a, t⟩ hz
  change augmented ω (f.prod 0) r (b, a, t) = 0 at hz
  have hsum := congrArg (fun p : A × A => f.range.mkQ (p.1 + ω • p.2)) hz
  have hfb : f.range.mkQ (f b) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
  have heq : (f b + ω • a + (trace ω r t).1) +
      ω • (-a + (trace ω r t).2) =
      f b + ((trace ω r t).1 + ω • (trace ω r t).2) := by
    simp only [smul_add, smul_neg]
    abel
  rw [augmented_apply] at hsum
  simp only [Prod.fst_zero, Prod.snd_zero, smul_zero, add_zero, map_zero] at hsum
  change f.range.mkQ ((f b + ω • a + (trace ω r t).1) +
    ω • (0 - a + (trace ω r t).2)) = 0 at hsum
  simp only [zero_sub] at hsum
  rw [heq, trace_contract, map_add, hfb, zero_add, map_sum] at hsum
  simp only [map_smul] at hsum
  have ht : t = 0 := scalarCoefficients_eq_zero ω hω hω1 t
    (funext (Fintype.linearIndependent_iff.mp hr _ hsum))
  have ha : a = 0 := by
    simpa [ht] using congrArg Prod.snd hz
  have hb : b = 0 := by
    apply hf
    simpa [ha, ht] using congrArg Prod.fst hz
  change (b, a, t) = 0
  simp [hb, ha, ht]

/-- The fourth trace needs one additional dimension in the quotient budget. -/
theorem exists_motions [FiniteDimensional K A]
    (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (f : V →ₗ[K] A) (hf : Function.Injective f)
    (hbudget : finrank K V + 4 ≤ finrank K A) :
    ∃ r : Fin 4 → A, Function.Injective (augmented ω (f.prod 0) r) := by
  let C := f.range
  have hc : finrank K C = finrank K V := LinearMap.finrank_range_of_inj hf
  have hquot := C.finrank_quotient_add_finrank
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank
    (show 4 ≤ finrank K (A ⧸ C) by omega)
  let r : Fin 4 → A := fun i => Classical.choose (C.mkQ_surjective (s i))
  have hr : (fun i => C.mkQ (r i)) = s := by
    funext i
    exact Classical.choose_spec (C.mkQ_surjective (s i))
  exact ⟨r, augmented_injective ω hω hω1 f hf r (hr ▸ hs)⟩

theorem exists_quotient_motions [FiniteDimensional K A]
    (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (f : V →ₗ[K] A) (hf : Function.Injective f) (q : ℕ)
    (hbudget : q + finrank K V + 4 ≤ finrank K A) :
    ∃ Q : Submodule K A, finrank K Q = q ∧ Function.Injective (quotientAlong f Q) ∧
      ∃ r : Fin 4 → A ⧸ Q,
        Function.Injective (augmented ω ((quotientAlong f Q).prod 0) r) := by
  have hrange : finrank K f.range = finrank K V := LinearMap.finrank_range_of_inj hf
  obtain ⟨Q, hQ, hdis⟩ := exists_disjoint_subspace f.range q (by omega)
  have hfQ := quotientAlong_injective f hf Q hdis
  have hdim := Q.finrank_quotient_add_finrank
  obtain ⟨r, hinj⟩ := exists_motions ω hω hω1 (quotientAlong f Q) hfQ (by omega)
  exact ⟨Q, hQ, hfQ, r, hinj⟩

theorem augmented_witness {m c q : ℕ} (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hc : c ≤ m) (hbudget : q + (c + 1).choose 2 + 4 ≤ (m + 1).choose 2) :
    LinearIndependent K (mixedFamily (K := K) hc) ∧
    ∃ Q : Submodule K (Forms K m 2), finrank K Q = q ∧
      Function.Injective (quotientAlong (activeForms hc 2) Q) ∧
      ∃ r : Fin 4 → Forms K m 2 ⧸ Q,
        Function.Injective (augmented ω ((quotientAlong (activeForms hc 2) Q).prod 0) r) := by
  refine ⟨mixedFamily_independent hc, ?_⟩
  exact exists_quotient_motions ω hω hω1
    (activeForms (K := K) hc 2) (activeForms_injective hc 2) q
    (by simpa only [finrank_quadrics] using hbudget)

end Quartic.ExtendedPureTrace
