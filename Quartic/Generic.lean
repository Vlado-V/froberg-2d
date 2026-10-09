module

public import Quartic.Homogeneous

@[expose] public section

/-!
# Precise generic target on ordered quadratic coefficients

A nonempty principal open is specified by one polynomial in the coefficients.
This avoids assuming a topology on the set of submodules. Its points are ordered
independent bases of the quadratic spaces in the manuscript. The universal
statement below is deliberately only a definition: it has not been proved.
-/

noncomputable section

namespace Quartic

variable (K : Type*) [Field K] (n r : ℕ)

abbrev CoefficientIndex := Fin r × Sym (Fin n) 2

/-- Interpret a full array of quadratic coefficients as actual homogeneous forms. -/
def coefficientQuadrics (a : CoefficientIndex n r → K) (i : Fin r) : Forms K n 2 :=
  (formsBasis K n 2).equivFun.symm (fun m => a (i, m))

def coefficientSpace (a : CoefficientIndex n r → K) : Submodule K (Poly K n) :=
  Submodule.span K (Set.range (fun i => (coefficientQuadrics K n r a i).val))

theorem coefficientSpace_quadratic (a : CoefficientIndex n r → K) :
    coefficientSpace K n r a ≤ Forms K n 2 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (coefficientQuadrics K n r a i).property

/-- The asserted rank/dimension on a nonempty principal Zariski-open set of
ordered coefficient arrays. Both independence and the actual quotient dimension
are required, so this is stronger than a naked numerical identity. -/
def GenericQuartic (n r : ℕ) : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex n r) K,
    (∃ a : CoefficientIndex n r → K, MvPolynomial.eval a D ≠ 0) ∧
    ∀ a : CoefficientIndex n r → K, MvPolynomial.eval a D ≠ 0 →
      LinearIndependent K (fun i => (coefficientQuadrics K n r a i).val) ∧
      Module.finrank K (QuarticQuotient K n (coefficientSpace K n r a)) =
        expectedDimension n r

/-- Exact generic target of the formalization. In the manuscript the field is
characteristic zero; a proof is intended for `[CharZero K]`. -/
def MainGenericStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : ℕ, r ≤ (n + 1).choose 2 → GenericQuartic K n r

theorem generic_implies_witness (h : GenericQuartic K n r) : QuarticWitness K n r := by
  obtain ⟨D, ⟨a, ha⟩, hD⟩ := h
  obtain ⟨hlin, hdim⟩ := hD a ha
  refine ⟨coefficientSpace K n r a, coefficientSpace_quadratic K n r a, ?_, hdim⟩
  change Module.finrank K (Submodule.span K
    (Set.range (fun i => (coefficientQuadrics K n r a i).val))) = r
  rw [finrank_span_eq_card hlin, Fintype.card_fin]

theorem main_generic_implies_witness (h : MainGenericStatement K) : MainWitnessStatement K := by
  intro n hn r hr
  exact generic_implies_witness K n r (h n hn r hr)

theorem generic_zero_generators : GenericQuartic K n 0 := by
  refine ⟨1, ⟨fun _ => 0, by simp⟩, ?_⟩
  intro a _
  refine ⟨linearIndependent_empty_type, ?_⟩
  have hspace : coefficientSpace K n 0 a = ⊥ := by
    simp [coefficientSpace]
  rw [hspace]
  change Module.finrank K ((Forms K n 4) ⧸ quarticProducts K n ⊥) = expectedDimension n 0
  rw [quarticProducts_bot,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule K (Forms K n 4)) rfl).finrank_eq]
  simp [expectedDimension, finrank_quartics]

theorem generic_one_generator (hn : 1 ≤ n) : GenericQuartic K n 1 := by
  let i : Fin n := ⟨0, by omega⟩
  let m : Sym (Fin n) 2 := Sym.replicate 2 i
  refine ⟨MvPolynomial.X (0, m), ⟨fun _ => 1, by simp⟩, ?_⟩
  intro a ha
  have hcoeff : a (0, m) ≠ 0 := by simpa using ha
  have hf : (coefficientQuadrics K n 1 a 0).val ≠ 0 := by
    intro hz
    have hzero : coefficientQuadrics K n 1 a 0 = 0 := Subtype.ext hz
    have h := congrArg (fun f : Forms K n 2 => (formsBasis K n 2).equivFun f m) hzero
    simp only [coefficientQuadrics, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] at h
    exact hcoeff h
  constructor
  · exact linearIndependent_unique_iff.mpr hf
  · have hspace : coefficientSpace K n 1 a =
        Submodule.span K {(coefficientQuadrics K n 1 a 0).val} := by
      simp [coefficientSpace, Set.range_unique]
    rw [hspace]
    exact single_quadric_quotient _ hf

end Quartic
