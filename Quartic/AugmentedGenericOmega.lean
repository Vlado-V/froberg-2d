module

public import Quartic.AugmentedMiddleOmega
public import Quartic.AugmentedGeneric
public import Quartic.PolynomialRankOpen

@[expose] public section

/-!
# Polynomial opens with the distinguished direction `ωu-v`

A fixed-space lifted map absorbs the moving child quotient. Its injectivity
implies injectivity of the augmented map on the actual quotient. The product
map is actual homogeneous polynomial substitution, hence quadratic in the
mixed coefficients.
-/
noncomputable section
namespace Quartic.AugmentedGenericOmega
open Module MvPolynomial HomologyCoordinates AugmentedMiddle AugmentedGeneric
set_option maxHeartbeats 1200000
variable {K : Type*} [Field K]
variable (ω : K)

section QuotientBridge
variable {S A : Type*} [AddCommGroup S] [Module K S]
  [AddCommGroup A] [Module K A] {q : ℕ}

/-- Augmentation of an arbitrary actual symmetric-product map. -/
def augmented (F : S →ₗ[K] A × A) (r : Fin 4 → A) :
    (S × (A × BlockHomology K)) →ₗ[K] A × A :=
  F.coprod (((ω • LinearMap.id : A →ₗ[K] A).prod (-LinearMap.id)).coprod (pureTrace r))

@[simp] theorem augmented_apply (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (b : S) (a : A) (ξ : BlockHomology K) :
    augmented ω F r (b, a, ξ) = ((F b).1 + ω • a + (pureTrace r ξ).1,
      (F b).2 - a + (pureTrace r ξ).2) := by
  apply Prod.ext <;> simp [augmented, sub_eq_add_neg, add_assoc]

/-- Scalar combinations of the actual ordered child generators. -/
def childSum (h : Fin q → A) : (Fin q → K) →ₗ[K] A where
  toFun t := ∑ i, t i • h i
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [smul_smul, Finset.smul_sum]

/-- Fixed target and source: only the first coordinate needs added child columns. -/
def lifted (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A) :
    ((S × (A × BlockHomology K)) × (Fin q → K)) →ₗ[K] A × A :=
  (augmented ω F r).coprod ((childSum h).prod 0)

@[simp] theorem lifted_apply (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A)
    (b : S) (a : A) (ξ : BlockHomology K) (t : Fin q → K) :
    lifted ω F h r ((b, a, ξ), t) = augmented ω F r (b, a, ξ) + (childSum h t, 0) := rfl

/-- The actual parameterized augmented map modulo the span of the child generators. -/
def quotientAugmented (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A) :
    let Q := Submodule.span K (Set.range h)
    (S × ((A ⧸ Q) × BlockHomology K)) →ₗ[K] (A ⧸ Q) × (A ⧸ Q) :=
  let Q := Submodule.span K (Set.range h)
  augmented ω ((Q.mkQ.prodMap Q.mkQ).comp F) (fun i => Q.mkQ (r i))

theorem quotientAugmented_span_eq (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A)
    (Q : Submodule K A) (hQ : Submodule.span K (Set.range h) = Q) :
    Function.Injective (quotientAugmented ω F h r) ↔
      Function.Injective (augmented ω ((Q.mkQ.prodMap Q.mkQ).comp F) (fun i => Q.mkQ (r i))) := by
  subst Q
  rfl

theorem pureTrace_map {A' : Type*} [AddCommGroup A'] [Module K A'] (L : A →ₗ[K] A')
    (r : Fin 4 → A) (ξ : BlockHomology K) :
    (L.prodMap L) (pureTrace r ξ) = pureTrace (fun i => L (r i)) ξ := by
  apply Prod.ext <;> simp [pureTrace, map_sum]

theorem augmented_quotient (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A)
    (b : S) (a : A) (ξ : BlockHomology K) :
    let Q := Submodule.span K (Set.range h)
    (Q.mkQ.prodMap Q.mkQ) (augmented ω F r (b, a, ξ)) =
      quotientAugmented ω F h r (b, Q.mkQ a, ξ) := by
  let Q := Submodule.span K (Set.range h)
  have ht := pureTrace_map Q.mkQ r ξ
  have ht₁ : Q.mkQ (pureTrace r ξ).1 = (pureTrace (fun i => Q.mkQ (r i)) ξ).1 := congrArg Prod.fst ht
  have ht₂ : Q.mkQ (pureTrace r ξ).2 = (pureTrace (fun i => Q.mkQ (r i)) ξ).2 := congrArg Prod.snd ht
  simp only [quotientAugmented, augmented_apply]
  apply Prod.ext
  · change Q.mkQ ((F b).1 + ω • a + (pureTrace r ξ).1) =
      Q.mkQ (F b).1 + ω • Q.mkQ a + (pureTrace (fun i => Q.mkQ (r i)) ξ).1
    rw [map_add, map_add, map_smul, ht₁]
  · change Q.mkQ ((F b).2 - a + (pureTrace r ξ).2) =
      Q.mkQ (F b).2 - Q.mkQ a + (pureTrace (fun i => Q.mkQ (r i)) ξ).2
    rw [map_add, map_sub, ht₂]

theorem childSum_mem (h : Fin q → A) (t : Fin q → K) :
    childSum h t ∈ Submodule.span K (Set.range h) := by
  change (∑ i, t i • h i) ∈ Submodule.span K (Set.range h)
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem lifted_injective_of_quotient (F : S →ₗ[K] A × A)
    (h : Fin q → A) (r : Fin 4 → A) (hh : LinearIndependent K h)
    (hq : Function.Injective (quotientAugmented ω F h r)) : Function.Injective (lifted ω F h r) := by
  let Q := Submodule.span K (Set.range h)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨⟨b, a, ξ⟩, t⟩ hz
  change lifted ω F h r ((b, a, ξ), t) = 0 at hz
  have hquot := congrArg (Q.mkQ.prodMap Q.mkQ) hz
  rw [lifted_apply, map_add, augmented_quotient] at hquot
  have hc : (Q.mkQ.prodMap Q.mkQ) (childSum h t, 0) = 0 := by
    apply Prod.ext
    · exact (Submodule.Quotient.mk_eq_zero Q).mpr (childSum_mem h t)
    · change Q.mkQ (0 : A) = 0
      exact map_zero _
  rw [hc, add_zero, map_zero] at hquot
  have he : (b, Q.mkQ a, ξ) = 0 := hq (hquot.trans (map_zero _).symm)
  have hb : b = 0 := congrArg Prod.fst he
  have hξ : ξ = 0 := congrArg (fun z => z.2.2) he
  have ha : a = 0 := by
    simpa [hb, hξ] using congrArg Prod.snd hz
  have ht : t = 0 := by
    have hs : ∑ i, t i • h i = 0 := by
      simpa [hb, hξ, ha, childSum] using congrArg Prod.fst hz
    funext i
    exact Fintype.linearIndependent_iff.mp hh t hs i
  change ((b, a, ξ), t) = 0
  simp [hb, ha, hξ, ht]

/-- Injectivity on the fixed polynomial spaces descends to the moving actual quotient. -/
theorem quotient_injective_of_lifted (F : S →ₗ[K] A × A)
    (h : Fin q → A) (r : Fin 4 → A)
    (hl : Function.Injective (lifted ω F h r)) : Function.Injective (quotientAugmented ω F h r) := by
  let Q := Submodule.span K (Set.range h)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨b, a₀, ξ⟩ hz
  obtain ⟨a, rfl⟩ := Q.mkQ_surjective a₀
  change quotientAugmented ω F h r (b, Q.mkQ a, ξ) = 0 at hz
  let v := augmented ω F r (b, a, ξ)
  have hv : (Q.mkQ.prodMap Q.mkQ) v = 0 := by
    change (Q.mkQ.prodMap Q.mkQ) (augmented ω F r (b, a, ξ)) = 0
    rw [augmented_quotient, hz]
  have hv₁ : v.1 ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp (congrArg Prod.fst hv)
  have hv₂ : v.2 ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp (congrArg Prod.snd hv)
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (Q.neg_mem (Q.add_mem hv₁ (Q.smul_mem ω hv₂)))
  have hshift : augmented ω F r (b, a + v.2, ξ) = v + (ω • v.2, -v.2) := by
    apply Prod.ext <;> simp only [augmented_apply, Prod.fst_add, Prod.snd_add, v]
    all_goals try simp only [smul_add]
    all_goals abel
  have ht' : childSum h t = -(v.1 + ω • v.2) := ht
  have hzero : lifted ω F h r ((b, a + v.2, ξ), t) = 0 := by
    rw [lifted_apply, hshift, ht']
    apply Prod.ext <;> simp
  have he : ((b, a + v.2, ξ), t) = 0 := hl (hzero.trans (map_zero _).symm)
  have hb : b = 0 := congrArg (fun z => z.1.1) he
  have hξ : ξ = 0 := congrArg (fun z => z.1.2.2) he
  have ha : a + v.2 = 0 := congrArg (fun z => z.1.2.1) he
  have ha₀ : Q.mkQ a = 0 := by
    have heq := congrArg Q.mkQ ha
    have hv₂' : Q.mkQ v.2 = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hv₂
    simpa only [map_add, hv₂', map_zero, add_zero] using heq
  change (b, Q.mkQ a, ξ) = 0
  simp [hb, ha₀, hξ]

/-- The fixed-space lifted matrix is polynomial whenever its product and coefficient families are. -/
theorem lifted_polynomial {ι : Type*} [FiniteDimensional K S] [FiniteDimensional K A]
    (F : (ι → K) → (S →ₗ[K] A × A)) (h : (ι → K) → Fin q → A)
    (r : (ι → K) → Fin 4 → A) (hF : IsPolynomialFamily F)
    (hh : ∀ i, IsPolynomialFamily (fun a => h a i))
    (hr : ∀ i, IsPolynomialFamily (fun a => r a i)) :
    IsPolynomialFamily (fun a => lifted ω (F a) (h a) (r a)) := by
  apply isPolynomialFamily_linearMap
  rintro ⟨⟨b, a, ξ⟩, t⟩
  have hp := hF.linear_comp (LinearMap.applyₗ (R := K) (M₂ := A × A) b)
  have ht₁ := IsPolynomialFamily.sum (fun i : Fin 4 =>
    (isPolynomialFamily_const (ι := ι) (homologyReduction ξ i).1).smul (hr i))
  have ht₂ := IsPolynomialFamily.sum (fun i : Fin 4 =>
    (isPolynomialFamily_const (ι := ι) (homologyReduction ξ i).2).smul (hr i))
  have htrace := ht₁.prod_mk ht₂
  have hc := (IsPolynomialFamily.sum (fun i : Fin q =>
    (isPolynomialFamily_const (ι := ι) (t i)).smul (hh i))).prod_mk
      (isPolynomialFamily_const (ι := ι) (0 : A))
  have hall := ((hp.add (isPolynomialFamily_const (ι := ι) (ω • a, -a))).add htrace).add hc
  simpa [lifted, augmented, childSum, pureTrace, add_assoc] using hall

end QuotientBridge
section Coefficients
variable {m c q : ℕ}
/-- The actual full matrix family on fixed homogeneous polynomial spaces. -/
def liftedFamily (a : ParameterIndex m c q → K) :
    LiftedSource K m c q →ₗ[K] (Forms K m 2 × Forms K m 2) :=
  lifted ω (productMap (coefficientMixed a)) (coefficientChild a) (coefficientMotions a)

theorem liftedFamily_polynomial : IsPolynomialFamily (liftedFamily ω (K := K) (m := m) (c := c) (q := q)) := by
  classical
  apply lifted_polynomial ω
  · apply productMap_polynomial
    intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMixed)
  · intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientChild)
  · intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMotions)

/-- The concrete parameterized augmented witness gives an actual full-coefficient injective point. -/
theorem exists_injective_parameter (hc : c ≤ m)
    (hbudget : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ∃ a : ParameterIndex m c q → K,
      LinearIndependent K (coefficientMixed a) ∧ LinearIndependent K (coefficientChild a) ∧
      Function.Injective (liftedFamily ω a) := by
  obtain ⟨hg, Q, hQ, _, r, _, hr, _⟩ := AugmentedMiddleOmega.augmented_witness ω hω hω1 hc hbudget
  obtain ⟨h, hh, hspan⟩ := MiddleGeneric.family_of_submodule Q hQ
  let r₀ : Fin 4 → Forms K m 2 := fun i => Classical.choose (Q.mkQ_surjective (r i))
  have hr₀ : (fun i => Q.mkQ (r₀ i)) = r := funext (fun i => Classical.choose_spec (Q.mkQ_surjective (r i)))
  have hquot : Function.Injective (quotientAugmented ω (productMap (mixedFamily hc)) h r₀) := by
    apply (quotientAugmented_span_eq ω _ h r₀ Q hspan).mpr
    rw [productMap_specialization, hr₀]
    exact hr

  refine ⟨encode (mixedFamily hc) h r₀, ?_, ?_, ?_⟩
  · simpa only [coefficientMixed_encode] using hg
  · simpa only [coefficientChild_encode] using hh
  · simpa only [liftedFamily, coefficientMixed_encode, coefficientChild_encode, coefficientMotions_encode] using
      lifted_injective_of_quotient ω (productMap (mixedFamily hc)) h r₀ hh hquot

/-- A principal open in the actual full monomial coefficient space. -/
def GenericAugmented (K : Type*) [Field K] (ω : K) (m c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex m c q) K, (∃ a₀, eval a₀ D ≠ 0) ∧
    ∀ a, eval a D ≠ 0 → LinearIndependent K (coefficientMixed a) ∧
      LinearIndependent K (coefficientChild a) ∧ Function.Injective
        (quotientAugmented ω (productMap (coefficientMixed a)) (coefficientChild a) (coefficientMotions a))

/-- The source parameterized augmented numerical budget supplies a nonempty determinant open,
with the actual quotient, actual symmetric products, and actual pure homology. -/
theorem genericAugmented_of_budget (hc : c ≤ m)
    (hbudget : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    GenericAugmented K ω m c q := by
  classical
  obtain ⟨a₀, hg, hh, hi⟩ := exists_injective_parameter ω hc hbudget hω hω1
  obtain ⟨Dg, hDg, hpg⟩ := independent_polynomial_principal_open
    (fun i a => coefficientMixed (K := K) (m := m) (c := c) (q := q) a i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMixed)) a₀ hg
  obtain ⟨Dh, hDh, hph⟩ := independent_polynomial_principal_open
    (fun i a => coefficientChild (K := K) (m := m) (c := c) (q := q) a i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientChild)) a₀ hh
  obtain ⟨Dl, hDl, hpl⟩ := injective_polynomial_principal_open
    (liftedFamily ω (K := K) (m := m) (c := c) (q := q))
    (liftedFamily_polynomial ω (K := K) (m := m) (c := c) (q := q)) a₀ hi
  refine ⟨Dg * Dh * Dl, ⟨a₀, by simpa only [map_mul] using mul_ne_zero (mul_ne_zero hDg hDh) hDl⟩, ?_⟩
  intro a ha
  simp only [map_mul, mul_ne_zero_iff] at ha
  exact ⟨hpg a ha.1.1, hph a ha.1.2, quotient_injective_of_lifted ω _ _ _ (hpl a ha.2)⟩

end Coefficients

end Quartic.AugmentedGenericOmega
