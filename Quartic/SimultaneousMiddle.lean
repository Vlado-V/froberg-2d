import Quartic.AugmentedGeneric

/-!
# A common nonempty middle and augmented parameter open

The middle determinant is pulled back to the full mixed/child/motion
coefficient space without changing the shared generator families. Over an
infinite field it can be imposed simultaneously with the augmented determinant.
No child endpoint or incidence condition is asserted here.
-/
noncomputable section
namespace Quartic.SimultaneousMiddle
open MvPolynomial AugmentedGeneric
set_option maxHeartbeats 300000
variable {K : Type*} [Field K] {m c q : ℕ}

/-- Forget the four pure-motion coefficient blocks. -/
def baseCoefficients (a : ParameterIndex m c q → K) : MiddleCoordinates.CoefficientIndex m c q → K :=
  fun i => a (Sum.inl i)

/-- Extend a middle coefficient point with zero pure motions. -/
def zeroMotionExtension (a : MiddleCoordinates.CoefficientIndex m c q → K) : ParameterIndex m c q → K :=
  Sum.elim a (fun _ => 0)

@[simp] theorem baseCoefficients_extension (a : MiddleCoordinates.CoefficientIndex m c q → K) :
    baseCoefficients (zeroMotionExtension a) = a := rfl

@[simp] theorem coefficientBase_eq (a : ParameterIndex m c q → K) :
    coefficientBase a = MiddleCoordinates.decode (baseCoefficients a) := rfl

@[simp] theorem coefficientMixed_eq (a : ParameterIndex m c q → K) :
    coefficientMixed a = (MiddleCoordinates.decode (baseCoefficients a)).1 := rfl

@[simp] theorem coefficientChild_eq (a : ParameterIndex m c q → K) :
    coefficientChild a = (MiddleCoordinates.decode (baseCoefficients a)).2 := rfl

/-- Pull the actual middle determinant back along the common coefficient projection. -/
def middlePullback (D : MvPolynomial (MiddleCoordinates.CoefficientIndex m c q) K) :
    MvPolynomial (ParameterIndex m c q) K := MvPolynomial.rename Sum.inl D

@[simp] theorem eval_middlePullback (a : ParameterIndex m c q → K)
    (D : MvPolynomial (MiddleCoordinates.CoefficientIndex m c q) K) :
    eval a (middlePullback D) = eval (baseCoefficients a) D := eval_rename _ _ _

/-- Both actual quotient-map properties hold on exactly the same generators. -/
def Both (a : ParameterIndex m c q → K) : Prop :=
  LinearIndependent K (coefficientMixed a) ∧ LinearIndependent K (coefficientChild a) ∧
  Function.Surjective (MiddleCoordinates.quotientMap (coefficientMixed a)
    (Submodule.span K (Set.range (coefficientChild a)))) ∧
  Function.Injective (quotientAugmented (productMap (coefficientMixed a))
    (coefficientChild a) (coefficientMotions a))

/-- The common rank condition is itself a nonempty principal open. -/
def GenericBoth (K : Type*) [Field K] (m c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex m c q) K,
    (∃ a₀, eval a₀ D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → Both a

theorem genericBoth_of_generic [Infinite K]
    (hmid : MiddleCoordinates.GenericMiddle K m c q)
    (haug : GenericAugmented K m c q) : GenericBoth K m c q := by
  classical
  obtain ⟨Dm, ⟨am, ham⟩, hm⟩ := hmid
  obtain ⟨Da, ⟨aa, haa⟩, ha⟩ := haug
  have hDa : Da ≠ 0 := by intro h; simp [h] at haa
  have hDp : middlePullback Dm ≠ 0 := by
    intro h
    have he : eval (zeroMotionExtension am) (middlePullback Dm) ≠ 0 := by
      simpa only [eval_middlePullback, baseCoefficients_extension] using ham
    simp [h] at he
  obtain ⟨a₀, h₀⟩ := nonempty_principal_intersection
    (![Da, middlePullback Dm] : Fin 2 → MvPolynomial (ParameterIndex m c q) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨Da * middlePullback Dm, ⟨a₀, ?_⟩, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero (h₀ 0) (h₀ 1)
  · intro a hn
    rw [map_mul] at hn
    obtain ⟨hna, hnm⟩ := mul_ne_zero_iff.mp hn
    obtain ⟨hg, hh, hinj⟩ := ha a hna
    rw [eval_middlePullback] at hnm
    have hsurj := (hm (baseCoefficients a) hnm).2.2
    exact ⟨hg, hh, hsurj, hinj⟩

/-- The manuscript's numerical middle and augmented budgets give a common
nonempty determinant open in the full actual coefficient space. -/
theorem genericBoth_of_budgets [Infinite K] (hc : c ≤ m)
    (haug : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2)
    (hmid : ((m + 1) / 2 ≤ c ∧ c ≤ 3*m) ∨
      (2*c ≤ m ∧ c*(m-2*c) + (m-2*c+1).choose 2 ≤ q))
    (h2 : (2 : K) ≠ 0) : GenericBoth K m c q :=
  genericBoth_of_generic (MiddleCoordinates.genericMiddle_of_budgets (by omega) hmid)
    (genericAugmented_of_budget hc haug h2)

theorem exists_simultaneous_of_budgets [Infinite K] (hc : c ≤ m)
    (haug : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2)
    (hmid : ((m + 1) / 2 ≤ c ∧ c ≤ 3*m) ∨
      (2*c ≤ m ∧ c*(m-2*c) + (m-2*c+1).choose 2 ≤ q))
    (h2 : (2 : K) ≠ 0) : ∃ a : ParameterIndex m c q → K, Both a := by
  obtain ⟨D, ⟨a, ha⟩, h⟩ := genericBoth_of_budgets hc haug hmid h2
  exact ⟨a, h a ha⟩

end Quartic.SimultaneousMiddle
