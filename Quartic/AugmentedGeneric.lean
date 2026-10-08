import Quartic.AugmentedMiddle
import Quartic.PolynomialRankOpen

/-!
# Polynomial opens for actual augmented middle multiplication

A fixed-space lifted map absorbs the moving child quotient. Its injectivity
implies injectivity of the augmented map on the actual quotient. The product
map is actual homogeneous polynomial substitution, hence quadratic in the
mixed coefficients.
-/
noncomputable section
namespace Quartic.AugmentedGeneric
open Module MvPolynomial HomologyCoordinates AugmentedMiddle
set_option maxHeartbeats 500000
variable {K : Type*} [Field K]

section QuotientBridge
variable {S A : Type*} [AddCommGroup S] [Module K S]
  [AddCommGroup A] [Module K A] {q : ℕ}

/-- Augmentation of an arbitrary actual symmetric-product map. -/
def augmented (F : S →ₗ[K] A × A) (r : Fin 4 → A) :
    (S × (A × BlockHomology K)) →ₗ[K] A × A :=
  F.coprod (((LinearMap.id : A →ₗ[K] A).prod (-LinearMap.id)).coprod (pureTrace r))

@[simp] theorem augmented_apply (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (b : S) (a : A) (ξ : BlockHomology K) :
    augmented F r (b, a, ξ) = ((F b).1 + a + (pureTrace r ξ).1,
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
  (augmented F r).coprod ((childSum h).prod 0)

@[simp] theorem lifted_apply (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A)
    (b : S) (a : A) (ξ : BlockHomology K) (t : Fin q → K) :
    lifted F h r ((b, a, ξ), t) = augmented F r (b, a, ξ) + (childSum h t, 0) := rfl

/-- The actual augmented map modulo the span of the child generators. -/
def quotientAugmented (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A) :
    let Q := Submodule.span K (Set.range h)
    (S × ((A ⧸ Q) × BlockHomology K)) →ₗ[K] (A ⧸ Q) × (A ⧸ Q) :=
  let Q := Submodule.span K (Set.range h)
  augmented ((Q.mkQ.prodMap Q.mkQ).comp F) (fun i => Q.mkQ (r i))

theorem quotientAugmented_span_eq (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A)
    (Q : Submodule K A) (hQ : Submodule.span K (Set.range h) = Q) :
    Function.Injective (quotientAugmented F h r) ↔
      Function.Injective (augmented ((Q.mkQ.prodMap Q.mkQ).comp F) (fun i => Q.mkQ (r i))) := by
  subst Q
  rfl

theorem pureTrace_map {A' : Type*} [AddCommGroup A'] [Module K A'] (L : A →ₗ[K] A')
    (r : Fin 4 → A) (ξ : BlockHomology K) :
    (L.prodMap L) (pureTrace r ξ) = pureTrace (fun i => L (r i)) ξ := by
  apply Prod.ext <;> simp [pureTrace, map_sum]

theorem augmented_quotient (F : S →ₗ[K] A × A) (h : Fin q → A) (r : Fin 4 → A)
    (b : S) (a : A) (ξ : BlockHomology K) :
    let Q := Submodule.span K (Set.range h)
    (Q.mkQ.prodMap Q.mkQ) (augmented F r (b, a, ξ)) =
      quotientAugmented F h r (b, Q.mkQ a, ξ) := by
  let Q := Submodule.span K (Set.range h)
  have ht := pureTrace_map Q.mkQ r ξ
  have ht₁ : Q.mkQ (pureTrace r ξ).1 = (pureTrace (fun i => Q.mkQ (r i)) ξ).1 := congrArg Prod.fst ht
  have ht₂ : Q.mkQ (pureTrace r ξ).2 = (pureTrace (fun i => Q.mkQ (r i)) ξ).2 := congrArg Prod.snd ht
  simp only [quotientAugmented, augmented_apply]
  apply Prod.ext
  · change Q.mkQ ((F b).1 + a + (pureTrace r ξ).1) =
      Q.mkQ (F b).1 + Q.mkQ a + (pureTrace (fun i => Q.mkQ (r i)) ξ).1
    rw [map_add, map_add, ht₁]
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
    (hq : Function.Injective (quotientAugmented F h r)) : Function.Injective (lifted F h r) := by
  let Q := Submodule.span K (Set.range h)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨⟨b, a, ξ⟩, t⟩ hz
  change lifted F h r ((b, a, ξ), t) = 0 at hz
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
    (hl : Function.Injective (lifted F h r)) : Function.Injective (quotientAugmented F h r) := by
  let Q := Submodule.span K (Set.range h)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨b, a₀, ξ⟩ hz
  obtain ⟨a, rfl⟩ := Q.mkQ_surjective a₀
  change quotientAugmented F h r (b, Q.mkQ a, ξ) = 0 at hz
  let v := augmented F r (b, a, ξ)
  have hv : (Q.mkQ.prodMap Q.mkQ) v = 0 := by
    change (Q.mkQ.prodMap Q.mkQ) (augmented F r (b, a, ξ)) = 0
    rw [augmented_quotient, hz]
  have hv₁ : v.1 ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp (congrArg Prod.fst hv)
  have hv₂ : v.2 ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp (congrArg Prod.snd hv)
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (Q.neg_mem (Q.add_mem hv₁ hv₂))
  have hshift : augmented F r (b, a + v.2, ξ) = v + (v.2, -v.2) := by
    apply Prod.ext <;> simp only [augmented_apply, Prod.fst_add, Prod.snd_add, v]
    all_goals abel
  have ht' : childSum h t = -(v.1 + v.2) := ht
  have hzero : lifted F h r ((b, a + v.2, ξ), t) = 0 := by
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
    IsPolynomialFamily (fun a => lifted (F a) (h a) (r a)) := by
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
  have hall := ((hp.add (isPolynomialFamily_const (ι := ι) (a, -a))).add htrace).add hc
  simpa [lifted, augmented, childSum, pureTrace, add_assoc] using hall

end QuotientBridge
section Products
variable {m c : ℕ}

/-- Substitute actual child linear forms in a homogeneous quadratic. -/
def quadSubstitute (l : Fin c → Forms K m 1) : Forms K c 2 →ₗ[K] Forms K m 2 where
  toFun b := ⟨MvPolynomial.aeval (fun i => (l i).val) b.val,
    by simpa using b.property.aeval (fun i => (l i).val) (fun i => (l i).property)⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (by simp)

/-- Actual symmetric products reduced modulo the fixed four pure quadrics. -/
def productMap (g : Fin c → MiddleCoordinates.Mixed K m) :
    Forms K c 2 →ₗ[K] (Forms K m 2 × Forms K m 2) :=
  ((quadSubstitute (fun i => g i 0)) - (quadSubstitute (fun i => g i 2))).prod
    ((quadSubstitute (fun i => g i 1)) - (quadSubstitute (fun i => g i 2)))

theorem productMap_monomial (g : Fin c → MiddleCoordinates.Mixed K m) (i j : Fin c) :
    productMap g (quadraticMonomial i j) = MiddleCoordinates.projectedProduct (g i) (g j) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [productMap, quadSubstitute, quadraticMonomial,
      MiddleCoordinates.projectedProduct, MiddleCoordinates.mulLinear]

private theorem span_subtype_of_span_value {V J : Type*} [AddCommGroup V] [Module K V]
    (S : Submodule K V) (f : J → S)
    (hf : Submodule.span K (Set.range (fun i => (f i).val)) = S) :
    Submodule.span K (Set.range f) = ⊤ := by
  let T := Submodule.span K (Set.range f)
  have ht : T.map S.subtype = S := by
    change (Submodule.span K (Set.range f)).map S.subtype = S
    rw [Submodule.map_span, ← Set.range_comp]
    exact hf
  apply top_unique
  intro b _
  have hb : b.val ∈ T.map S.subtype := by rw [ht]; exact b.property
  obtain ⟨d, hd, he⟩ := hb
  exact (Subtype.ext he) ▸ hd

private theorem polynomial_quadratic_span :
    Submodule.span K (Set.range (fun p : Fin c × Fin c => (X p.1 * X p.2 : Poly K c))) = Forms K c 2 := by
  rw [Forms, ← homogeneousSubmodule_one_pow K 2, pow_two,
    homogeneousSubmodule_one_eq_span_X, Submodule.span_mul_span]
  congr 1
  ext p
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, X j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨(i, j), rfl⟩

theorem quadraticMonomial_span :
    Submodule.span K (Set.range (fun p : Fin c × Fin c => quadraticMonomial (K := K) p.1 p.2)) = ⊤ := by
  apply span_subtype_of_span_value
  exact polynomial_quadratic_span

/-- The general product map recovers the actual witness specialization. -/
theorem productMap_specialization (hc : c ≤ m) :
    productMap (mixedFamily (K := K) hc) = (activeForms hc 2).prod 0 := by
  apply LinearMap.ext_on_range quadraticMonomial_span
  intro p
  rw [productMap_monomial, mixedFamily_product]
  rfl

/-- Bilinearity of the actual reduced product in both mixed inputs. -/
def mixedProduct : MiddleCoordinates.Mixed K m →ₗ[K]
    (MiddleCoordinates.Mixed K m →ₗ[K] (Forms K m 2 × Forms K m 2)) where
  toFun := MiddleCoordinates.projectedProduct
  map_add' g h := by
    apply LinearMap.ext
    intro b
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [MiddleCoordinates.projectedProduct, MiddleCoordinates.mulLinear, add_mul] <;> ring
  map_smul' s g := by
    apply LinearMap.ext
    intro b
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [MiddleCoordinates.projectedProduct, MiddleCoordinates.mulLinear, smul_sub]

variable {ι : Type*}
/-- The actual symmetric product matrix varies polynomially in mixed coefficients. -/
theorem productMap_polynomial (g : (ι → K) → (Fin c → MiddleCoordinates.Mixed K m))
    (hg : ∀ i, IsPolynomialFamily (fun a => g a i)) : IsPolynomialFamily (fun a => productMap (g a)) := by
  apply isPolynomialFamily_linearMap
  intro b
  have hb : b ∈ Submodule.span K (Set.range
      (fun p : Fin c × Fin c => quadraticMonomial (K := K) p.1 p.2)) := by rw [quadraticMonomial_span]; trivial
  refine Submodule.span_induction (p := fun b _ => IsPolynomialFamily (fun a => productMap (g a) b))
    ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    have he : (fun a => productMap (g a) (quadraticMonomial i j)) =
        (fun a => mixedProduct (K := K) (m := m) (g a i) (g a j)) := by
      funext a
      exact productMap_monomial (g a) i j
    rw [he]
    exact (hg i).bilinear (hg j) (mixedProduct (K := K) (m := m))
  · simpa only [map_zero] using (isPolynomialFamily_const (ι := ι) (0 : Forms K m 2 × Forms K m 2))
  · intro x y _ _ hx hy
    simpa only [map_add] using hx.add hy
  · intro s x _ hx
    simpa only [map_smul] using (isPolynomialFamily_const (ι := ι) s).smul hx

end Products

section Coefficients
variable (K : Type*) [Field K] (m c q : ℕ)

/-- Every coefficient of the mixed family, child quadrics, and four pure motions. -/
abbrev ParameterIndex := MiddleCoordinates.CoefficientIndex m c q ⊕ (Fin 4 × Sym (Fin m) 2)
abbrev LiftedSource := (Forms K c 2 × (Forms K m 2 × BlockHomology K)) × (Fin q → K)
variable {K m c q}

def coefficientBase : (ParameterIndex m c q → K) →ₗ[K]
    MiddleCoordinates.Parameters K m c q :=
  MiddleCoordinates.decode.toLinearMap.comp (LinearMap.pi (fun i => LinearMap.proj (Sum.inl i)))

def coefficientMixed : (ParameterIndex m c q → K) →ₗ[K] (Fin c → MiddleCoordinates.Mixed K m) :=
  (LinearMap.fst K _ _).comp coefficientBase

def coefficientChild : (ParameterIndex m c q → K) →ₗ[K] (Fin q → Forms K m 2) :=
  (LinearMap.snd K _ _).comp coefficientBase

def coefficientMotions : (ParameterIndex m c q → K) →ₗ[K] (Fin 4 → Forms K m 2) :=
  LinearMap.pi (fun i => (formsBasis K m 2).equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun j => LinearMap.proj (Sum.inr (i, j)))))

/-- The explicit coefficient point of any actual ordered families. -/
def encode (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2) : ParameterIndex m c q → K :=
  Sum.elim (MiddleCoordinates.decode.symm (g, h))
    (fun p => (formsBasis K m 2).equivFun (r p.1) p.2)

@[simp] theorem coefficientBase_encode (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2) :
    coefficientBase (encode g h r) = (g, h) := by
  change MiddleCoordinates.decode (MiddleCoordinates.decode.symm (g, h)) = (g, h)
  exact LinearEquiv.apply_symm_apply _ _

@[simp] theorem coefficientMixed_encode (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2) : coefficientMixed (encode g h r) = g := by
  exact congrArg Prod.fst (coefficientBase_encode g h r)

@[simp] theorem coefficientChild_encode (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2) : coefficientChild (encode g h r) = h := by
  exact congrArg Prod.snd (coefficientBase_encode g h r)

@[simp] theorem coefficientMotions_encode (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2) : coefficientMotions (encode g h r) = r := by
  funext i
  change (formsBasis K m 2).equivFun.symm ((formsBasis K m 2).equivFun (r i)) = r i
  exact LinearEquiv.symm_apply_apply _ _

/-- The actual full matrix family on fixed homogeneous polynomial spaces. -/
def liftedFamily (a : ParameterIndex m c q → K) :
    LiftedSource K m c q →ₗ[K] (Forms K m 2 × Forms K m 2) :=
  lifted (productMap (coefficientMixed a)) (coefficientChild a) (coefficientMotions a)

theorem liftedFamily_polynomial : IsPolynomialFamily (liftedFamily (K := K) (m := m) (c := c) (q := q)) := by
  classical
  apply lifted_polynomial
  · apply productMap_polynomial
    intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMixed)
  · intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientChild)
  · intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMotions)

/-- The concrete augmented witness gives an actual full-coefficient injective point. -/
theorem exists_injective_parameter (hc : c ≤ m)
    (hbudget : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2) (h2 : (2 : K) ≠ 0) :
    ∃ a : ParameterIndex m c q → K,
      LinearIndependent K (coefficientMixed a) ∧ LinearIndependent K (coefficientChild a) ∧
      Function.Injective (liftedFamily a) := by
  obtain ⟨hg, Q, hQ, _, r, _, hr, _⟩ := augmented_witness (K := K) hc hbudget h2
  obtain ⟨h, hh, hspan⟩ := MiddleGeneric.family_of_submodule Q hQ
  let r₀ : Fin 4 → Forms K m 2 := fun i => Classical.choose (Q.mkQ_surjective (r i))
  have hr₀ : (fun i => Q.mkQ (r₀ i)) = r := funext (fun i => Classical.choose_spec (Q.mkQ_surjective (r i)))
  have hquot : Function.Injective (quotientAugmented (productMap (mixedFamily hc)) h r₀) := by
    apply (quotientAugmented_span_eq _ h r₀ Q hspan).mpr
    rw [productMap_specialization, hr₀]
    exact hr

  refine ⟨encode (mixedFamily hc) h r₀, ?_, ?_, ?_⟩
  · simpa only [coefficientMixed_encode] using hg
  · simpa only [coefficientChild_encode] using hh
  · simpa only [liftedFamily, coefficientMixed_encode, coefficientChild_encode, coefficientMotions_encode] using
      lifted_injective_of_quotient (productMap (mixedFamily hc)) h r₀ hh hquot

/-- A principal open in the actual full monomial coefficient space. -/
def GenericAugmented (K : Type*) [Field K] (m c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex m c q) K, (∃ a₀, eval a₀ D ≠ 0) ∧
    ∀ a, eval a D ≠ 0 → LinearIndependent K (coefficientMixed a) ∧
      LinearIndependent K (coefficientChild a) ∧ Function.Injective
        (quotientAugmented (productMap (coefficientMixed a)) (coefficientChild a) (coefficientMotions a))

/-- The source augmented numerical budget supplies a nonempty determinant open,
with the actual quotient, actual symmetric products, and actual pure homology. -/
theorem genericAugmented_of_budget (hc : c ≤ m)
    (hbudget : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2) (h2 : (2 : K) ≠ 0) :
    GenericAugmented K m c q := by
  classical
  obtain ⟨a₀, hg, hh, hi⟩ := exists_injective_parameter hc hbudget h2
  obtain ⟨Dg, hDg, hpg⟩ := independent_polynomial_principal_open
    (fun i a => coefficientMixed (K := K) (m := m) (c := c) (q := q) a i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMixed)) a₀ hg
  obtain ⟨Dh, hDh, hph⟩ := independent_polynomial_principal_open
    (fun i a => coefficientChild (K := K) (m := m) (c := c) (q := q) a i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientChild)) a₀ hh
  obtain ⟨Dl, hDl, hpl⟩ := injective_polynomial_principal_open
    (liftedFamily (K := K) (m := m) (c := c) (q := q))
    (liftedFamily_polynomial (K := K) (m := m) (c := c) (q := q)) a₀ hi
  refine ⟨Dg * Dh * Dl, ⟨a₀, by simpa only [map_mul] using mul_ne_zero (mul_ne_zero hDg hDh) hDl⟩, ?_⟩
  intro a ha
  simp only [map_mul, mul_ne_zero_iff] at ha
  exact ⟨hpg a ha.1.1, hph a ha.1.2, quotient_injective_of_lifted _ _ _ (hpl a ha.2)⟩

end Coefficients

end Quartic.AugmentedGeneric
