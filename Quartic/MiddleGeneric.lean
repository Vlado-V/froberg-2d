import Quartic.SplitMiddle22
import Quartic.RankOpen

/-!
# Generic middle multiplication from the explicit polynomial witnesses

Parameters are actual mixed polynomials and child quadrics. The combined map
adds the child relations in both output coordinates, so its surjectivity is
equivalent to surjectivity of middle multiplication in the child quotient.
Its entries vary linearly with the parameters. The determinant neighborhoods
below are obtained from the concrete witnesses, rather than assumed ranks.
-/

noncomputable section
namespace Quartic.MiddleGeneric
open Module MvPolynomial SplitMiddle22
set_option maxHeartbeats 2000000

variable (K : Type*) [Field K] (c w r q : ℕ)
abbrev Mixed := Fin 3 → Linear K c w
abbrev Parameters := (Fin r → Mixed K c w) × (Fin q → Quad K c w)
abbrev Domain := (Fin r → Mixed K c w) × (Fin q → K × K)
variable {K c w r q}

/-- Linearity of actual projected multiplication in the mixed generator. -/
def productLinear : Mixed K c w →ₗ[K] (Mixed K c w →ₗ[K] Target K c w) where
  toFun := projectedProduct
  map_add' g h := by
    apply LinearMap.ext
    intro a
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [projectedProduct, mulLinear, add_mul] <;> ring
  map_smul' r g := by
    apply LinearMap.ext
    intro a
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [projectedProduct, mulLinear, smul_sub]

def multiplication (g : Fin r → Mixed K c w) : (Fin r → Mixed K c w) →ₗ[K] Target K c w :=
  ∑ i : Fin r, (productLinear (g i)).comp (LinearMap.proj i)

@[simp] theorem multiplication_single (g : Fin r → Mixed K c w) (i : Fin r) (a : Mixed K c w) :
    multiplication g (Pi.single i a) = projectedProduct (g i) a := by
  classical
  simp [multiplication, Pi.single_apply, apply_ite, productLinear]

/-- Scalar multiples of each child quadric in both pure-block coordinates. -/
def childMap (h : Fin q → Quad K c w) : (Fin q → K × K) →ₗ[K] Target K c w where
  toFun a := (∑ i, (a i).1 • h i, ∑ i, (a i).2 • h i)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' s a := by simp [smul_smul, Finset.smul_sum]

/-- The actual polynomial map whose full rank tests quotient surjectivity. -/
def combined (p : Parameters K c w r q) : Domain K c w r q →ₗ[K] Target K c w :=
  (multiplication p.1).coprod (childMap p.2)

/-- Dependence of every entry on the actual polynomial parameters is linear. -/
def combinedLinear : Parameters K c w r q →ₗ[K] (Domain K c w r q →ₗ[K] Target K c w) where
  toFun := combined
  map_add' p s := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have hm : multiplication (p.1 + s.1) a = multiplication p.1 a + multiplication s.1 a := by
      simp only [multiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    simp only [combined, LinearMap.add_apply, LinearMap.coprod_apply, Prod.fst_add, Prod.snd_add, hm,
      childMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, smul_add, Finset.sum_add_distrib]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' s p := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    have hm : multiplication (s • p.1) a = s • multiplication p.1 a := by
      simp only [multiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Pi.smul_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum]
    simp [combined, hm, childMap, smul_smul, Finset.smul_sum, smul_add, mul_comm]

/-- The multiplication image depends on the genuine span of the mixed generators. -/
theorem range_multiplication (g : Fin r → Mixed K c w) :
    LinearMap.range (multiplication g) = middleImage (Submodule.span K (Set.range g)) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    simp only [multiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.subset_span ⟨g i, Submodule.subset_span ⟨i, rfl⟩, a i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, a, rfl⟩
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact ⟨Pi.single i a, multiplication_single g i a⟩
    | zero =>
      have h : projectedProduct (0 : Mixed K c w) a = 0 :=
        congrArg (fun f : Mixed K c w →ₗ[K] Target K c w => f a) productLinear.map_zero
      rw [h]
      exact Submodule.zero_mem _
    | add f h hf hh ihf ihh =>
      have he : projectedProduct (f + h) a = projectedProduct f a + projectedProduct h a :=
        congrArg (fun f : Mixed K c w →ₗ[K] Target K c w => f a) (productLinear.map_add f h)
      rw [he]
      exact Submodule.add_mem _ ihf ihh
    | smul s f hf ih =>
      have he : projectedProduct (s • f) a = s • projectedProduct f a :=
        congrArg (fun f : Mixed K c w →ₗ[K] Target K c w => f a) (productLinear.map_smul s f)
      rw [he]
      exact Submodule.smul_mem _ s ih

/-- The child term has exactly the two copies of the child quadratic span as image. -/
theorem range_childMap (h : Fin q → Quad K c w) :
    LinearMap.range (childMap h) = (Submodule.span K (Set.range h)).prod
      (Submodule.span K (Set.range h)) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    constructor
    · change (∑ i, (a i).1 • h i) ∈ Submodule.span K (Set.range h)
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · change (∑ i, (a i).2 • h i) ∈ Submodule.span K (Set.range h)
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ha
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hb
    exact ⟨fun i => (ca i, cb i), Prod.ext hca hcb⟩

theorem range_combined (p : Parameters K c w r q) :
    LinearMap.range (combined p) = middleImage (Submodule.span K (Set.range p.1)) ⊔
      (Submodule.span K (Set.range p.2)).prod (Submodule.span K (Set.range p.2)) := by
  rw [combined, LinearMap.range_coprod, range_multiplication, range_childMap]

/-- A finite coordinate index for the actual coefficient parameter space. -/
abbrev ParameterIndex (K : Type*) [Field K] (c w r q : ℕ) :=
  Fin (Module.finrank K (Parameters K c w r q))

/-- Coordinates range over every actual tuple of mixed polynomials and child quadrics. -/
def decode : (ParameterIndex K c w r q → K) ≃ₗ[K] Parameters K c w r q :=
  (Module.finBasis K (Parameters K c w r q)).equivFun.symm

def coordinateMap : (ParameterIndex K c w r q → K) →ₗ[K]
    (Domain K c w r q →ₗ[K] Target K c w) :=
  combinedLinear.comp decode.toLinearMap

/-- The precise generic statement: a nonempty principal open of actual coefficients
has independent generator families and surjective combined polynomial multiplication. -/
def GenericMiddle (K : Type*) [Field K] (c w r q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex K c w r q) K,
    (∃ a₀, eval a₀ D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
      LinearIndependent K (decode a).1 ∧ LinearIndependent K (decode a).2 ∧
      Function.Surjective (combined (decode a))

/-- An actual independent, surjective witness produces the stated determinant open. -/
theorem genericMiddle_of_witness (p₀ : Parameters K c w r q)
    (hg : LinearIndependent K p₀.1) (hh : LinearIndependent K p₀.2)
    (hs : Function.Surjective (combined p₀)) : GenericMiddle K c w r q := by
  classical
  let a₀ := decode.symm p₀
  let G : Fin r → (ParameterIndex K c w r q → K) →ₗ[K] Mixed K c w :=
    fun i => (LinearMap.proj i).comp ((LinearMap.fst K _ _).comp decode.toLinearMap)
  let H : Fin q → (ParameterIndex K c w r q → K) →ₗ[K] Quad K c w :=
    fun i => (LinearMap.proj i).comp ((LinearMap.snd K _ _).comp decode.toLinearMap)
  have hg₀ : LinearIndependent K (fun i => G i a₀) := by simpa [G, a₀] using hg
  have hh₀ : LinearIndependent K (fun i => H i a₀) := by simpa [H, a₀] using hh
  obtain ⟨Dg, hDg, hopenG⟩ := independent_principal_open G a₀ hg₀
  obtain ⟨Dh, hDh, hopenH⟩ := independent_principal_open H a₀ hh₀
  obtain ⟨Dr, hDr, hopenR⟩ := rank_principal_open
    (coordinateMap (K := K) (c := c) (w := w) (r := r) (q := q)) a₀
  refine ⟨Dg * Dh * Dr, ⟨a₀, by simp only [map_mul]; exact mul_ne_zero (mul_ne_zero hDg hDh) hDr⟩, ?_⟩
  intro a ha
  have hparts : eval a Dg ≠ 0 ∧ eval a Dh ≠ 0 ∧ eval a Dr ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff, and_assoc] using ha
  refine ⟨by simpa [G] using hopenG a hparts.1,
    by simpa [H] using hopenH a hparts.2.1, ?_⟩
  have hr := hopenR a hparts.2.2
  have h₀ : coordinateMap a₀ = combined p₀ := by
    change combined (decode (decode.symm p₀)) = combined p₀
    rw [LinearEquiv.apply_symm_apply]
  rw [h₀, LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact Nat.le_antisymm (Submodule.finrank_le _) hr

section BasisFamily
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- Ordered polynomial coordinates for a subspace of a prescribed dimension. -/
theorem family_of_submodule (S : Submodule K V) (hS : Module.finrank K S = r) :
    ∃ f : Fin r → V, LinearIndependent K f ∧ Submodule.span K (Set.range f) = S := by
  let b := (Module.finBasis K S).reindex (finCongr hS)
  let f : Fin r → V := fun i => (b i).val
  have hlin : LinearIndependent K f := b.linearIndependent.map' S.subtype
    (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype S))
  refine ⟨f, hlin, ?_⟩
  have h := congrArg (Submodule.map S.subtype) b.span_eq
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype, Submodule.subtype_apply, f] using h

end BasisFamily

/-- The repaired paired-block specialization yields a nonempty determinant open
throughout the manuscript's second budget regime. -/
theorem genericMiddle_of_repair_budget
    (hlo : c * w + (w + 1).choose 2 ≤ q)
    (hhi : q ≤ (2 * c + w + 1).choose 2) : GenericMiddle K c w c q := by
  obtain ⟨Q, hQ, hdim⟩ := exists_extension_finrank (repairSpace (K := K) (c := c) (w := w)) q
    (by simpa [repairSpace_finrank] using hlo) (by simpa [quad_finrank] using hhi)
  obtain ⟨h, hh, hspan⟩ := family_of_submodule Q hdim
  apply genericMiddle_of_witness (mixedGenerator, h) mixedGenerator_independent hh
  apply LinearMap.range_eq_top.mp
  have heq : multiplication (mixedGenerator (K := K) (c := c) (w := w)) = middleMap := by
    apply Finset.sum_congr rfl
    intro i _
    rw [middleAt_eq_projectedProduct]
    rfl
  rw [combined, LinearMap.range_coprod, heq, range_childMap, hspan]
  exact filledSpace_eq_top Q (fun i b => hQ (repairSpace_contains_cross i b))
    (fun a b => hQ (repairSpace_contains_residual a b))

/-- The paired/singleton specialization yields the complete first regime:
any enlargement of its mixed space works, for every permitted child count. -/
theorem genericMiddle_of_covered_budget
    (hlo : c + w ≤ r) (hhi : r ≤ 3 * (2 * c + w))
    (hq : q ≤ (2 * c + w + 1).choose 2) : GenericMiddle K c w r q := by
  obtain ⟨E, hdim, hfill⟩ := middle_witness_of_covered_budget (K := K) r hlo hhi
  obtain ⟨g, hg, hspan⟩ := family_of_submodule E hdim
  obtain ⟨h, hh⟩ := exists_linearIndependent_of_le_finrank
    (show q ≤ Module.finrank K (Quad K c w) by simpa [quad_finrank] using hq)
  apply genericMiddle_of_witness (g, h) hg hh
  apply LinearMap.range_eq_top.mp
  rw [range_combined, hspan, hfill, top_sup_eq]

/-- Actual middle multiplication in both coordinates of the child quadratic quotient. -/
def quotientMultiplication (p : Parameters K c w r q) :
    (Fin r → Mixed K c w) →ₗ[K]
      ((Quad K c w ⧸ Submodule.span K (Set.range p.2)) ×
       (Quad K c w ⧸ Submodule.span K (Set.range p.2))) :=
  let Q := Submodule.span K (Set.range p.2)
  (Q.mkQ.prodMap Q.mkQ).comp (multiplication p.1)

theorem childMap_quotient_zero (h : Fin q → Quad K c w) (b : Fin q → K × K) :
    let Q := Submodule.span K (Set.range h)
    (Q.mkQ.prodMap Q.mkQ) (childMap h b) = 0 := by
  let Q := Submodule.span K (Set.range h)
  have hm : childMap h b ∈ Q.prod Q := by
    rw [← range_childMap]
    exact ⟨b, rfl⟩
  apply Prod.ext
  · exact (Submodule.Quotient.mk_eq_zero Q).mpr hm.1
  · exact (Submodule.Quotient.mk_eq_zero Q).mpr hm.2

/-- Full rank of the combined polynomial map is exactly quotient surjectivity. -/
theorem combined_surjective_iff_quotient (p : Parameters K c w r q) :
    Function.Surjective (combined p) ↔ Function.Surjective (quotientMultiplication p) := by
  let Q := Submodule.span K (Set.range p.2)
  constructor
  · intro hs
    rintro ⟨a, b⟩
    obtain ⟨a, rfl⟩ := Q.mkQ_surjective a
    obtain ⟨b, rfl⟩ := Q.mkQ_surjective b
    obtain ⟨⟨s, t⟩, hst⟩ := hs (a, b)
    refine ⟨s, ?_⟩
    have h := congrArg (Q.mkQ.prodMap Q.mkQ) hst
    change (Q.mkQ.prodMap Q.mkQ) (multiplication p.1 s + childMap p.2 t) = _ at h
    rw [map_add, childMap_quotient_zero, add_zero] at h
    exact h
  · intro hs ab
    obtain ⟨s, hs⟩ := hs ((Q.mkQ.prodMap Q.mkQ) ab)
    have hm : ab - multiplication p.1 s ∈ Q.prod Q := by
      have hz : (Q.mkQ.prodMap Q.mkQ) (ab - multiplication p.1 s) = 0 := by
        rw [map_sub]
        change (Q.mkQ.prodMap Q.mkQ) ab - quotientMultiplication p s = 0
        rw [hs, sub_self]
      exact ⟨(Submodule.Quotient.mk_eq_zero Q).mp (congrArg Prod.fst hz),
        (Submodule.Quotient.mk_eq_zero Q).mp (congrArg Prod.snd hz)⟩
    rw [← range_childMap] at hm
    obtain ⟨t, ht⟩ := hm
    refine ⟨(s, t), ?_⟩
    change multiplication p.1 s + childMap p.2 t = ab
    rw [ht]
    abel

/-- The nonempty determinant open really consists of independent generator
families with surjective multiplication in the actual child quadratic quotient. -/
theorem genericMiddle_quotient (h : GenericMiddle K c w r q) :
    ∃ D : MvPolynomial (ParameterIndex K c w r q) K,
      (∃ a₀, eval a₀ D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        LinearIndependent K (decode a).1 ∧ LinearIndependent K (decode a).2 ∧
        Function.Surjective (quotientMultiplication (decode a)) := by
  obtain ⟨D, hD, hopen⟩ := h
  refine ⟨D, hD, ?_⟩
  intro a ha
  obtain ⟨hg, hh, hs⟩ := hopen a ha
  exact ⟨hg, hh, (combined_surjective_iff_quotient _).mp hs⟩

end Quartic.MiddleGeneric
