import Froberg.Koszul
import Froberg.FormalProducts
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.BilinearMap

/-! Identification of the actual endpoint Koszul homology with formal-product relations. -/
noncomputable section
open TensorProduct Module
namespace Froberg

universe v w
variable {K : Type} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Z : Type w} [AddCommGroup Z] [Module K Z]

private def bilinearMultilinear (b : V →ₗ[K] V →ₗ[K] Z) :
    MultilinearMap K (fun _ : Fin 2 => V) Z where
  toFun a := b (a 0) (a 1)
  map_update_add' a i x y := by
    fin_cases i <;> simp [Function.update, map_add]
  map_update_smul' a i c x := by
    fin_cases i <;> simp [Function.update, map_smul]

private theorem bilinearMultilinear_symmetric (b : V →ₗ[K] V →ₗ[K] Z)
    (hb : ∀ a a', b a a' = b a' a) (e : Equiv.Perm (Fin 2)) (a : Fin 2 → V) :
    bilinearMultilinear b a = bilinearMultilinear b (fun i => a (e i)) := by
  have he : e 0 ≠ e 1 := e.injective.ne (by decide)
  generalize h0 : e 0 = i at *
  generalize h1 : e 1 = j at *
  fin_cases i <;> fin_cases j <;> simp_all [bilinearMultilinear]

private theorem bilinear_rel (b : V →ₗ[K] V →ₗ[K] Z)
    (hb : ∀ a a', b a a' = b a' a) (x y : ⨂[K] (_ : Fin 2), V)
    (h : addConGen (SymmetricPower.Rel K (Fin 2) V) x y) :
    PiTensorProduct.lift (bilinearMultilinear b) x =
      PiTensorProduct.lift (bilinearMultilinear b) y := by
  induction h with
  | of x y h =>
    cases h with
    | perm e a =>
      simpa only [PiTensorProduct.lift.tprod] using bilinearMultilinear_symmetric b hb e a
  | refl => rfl
  | symm => exact Eq.symm ‹_›
  | trans => exact Eq.trans ‹_› ‹_›
  | add => simp_all only [map_add]

/-- A symmetric bilinear map descends to mathlib's actual symmetric square quotient. -/
def symmetricBilinearLift (b : V →ₗ[K] V →ₗ[K] Z)
    (hb : ∀ a a', b a a' = b a' a) : SymmetricSquare K V →ₗ[K] Z where
  __ := AddCon.lift _ (PiTensorProduct.lift (bilinearMultilinear b)).toAddMonoidHom
    (fun x y h => bilinear_rel b hb x y h)
  map_smul' c x := AddCon.induction_on x fun x => by
    change PiTensorProduct.lift (bilinearMultilinear b) (c • x) =
      c • PiTensorProduct.lift (bilinearMultilinear b) x
    exact map_smul _ _ _

@[simp] theorem symmetricBilinearLift_symProd (b : V →ₗ[K] V →ₗ[K] Z)
    (hb : ∀ a a', b a a' = b a' a) (a a' : V) :
    symmetricBilinearLift b hb (symProd a a') = b a a' := by
  change PiTensorProduct.lift (bilinearMultilinear b) (PiTensorProduct.tprod K ![a, a']) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private def contractionBilinear (ℓ : V →ₗ[K] K) : V →ₗ[K] V →ₗ[K] V :=
  LinearMap.mk₂ K (fun a b => ℓ a • b + ℓ b • a)
    (by intros; simp [map_add, add_smul, smul_add]; abel)
    (by intros; simp [map_smul, smul_add, smul_smul, mul_comm])
    (by intros; simp [map_add, add_smul, smul_add]; abel)
    (by intros; simp [map_smul, smul_add, smul_smul, mul_comm])

/-- The contraction associated to a linear functional. -/
def symmetricContraction (ℓ : V →ₗ[K] K) : SymmetricSquare K V →ₗ[K] V :=
  symmetricBilinearLift (contractionBilinear ℓ) (by intros; exact add_comm _ _)

@[simp] theorem symmetricContraction_symProd (ℓ : V →ₗ[K] K) (a b : V) :
    symmetricContraction ℓ (symProd a b) = ℓ a • b + ℓ b • a :=
  symmetricBilinearLift_symProd _ _ a b

variable {r : ℕ}

/-- Formal multiplication of an ordered list by a coefficient array. -/
def formalCoefficientMap (q : Fin r → V) : (Fin r → V) →ₗ[K] SymmetricSquare K V :=
  ∑ i, (symProdLeft (K := K) (q i)).comp (LinearMap.proj i)

@[simp] theorem formalCoefficientMap_apply (q : Fin r → V) (a : Fin r → V) :
    formalCoefficientMap (K := K) q a = ∑ i, symProd (q i) (a i) := by
  simp only [formalCoefficientMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, symProdLeft]
  exact Finset.sum_congr rfl (fun i _ => symProd_comm _ _)

/-- The formal multiplication map kills every constant Koszul relation. -/
theorem formalCoefficientMap_koszul (q : Fin r → V) (p : GeneratorPair r) :
    formalCoefficientMap (K := K) q (koszulVector q p) = 0 := by
  classical
  rw [formalCoefficientMap_apply]
  simp only [koszulVector, symProd_sub_right]
  have hi (i j : Fin r) (v : V) :
      symProd (K := K) (q i) (if i = j then v else 0) =
        if i = j then symProd (q i) v else 0 := by split_ifs <;> simp_all
  simp only [hi, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sub_eq_zero.mpr (symProd_comm _ _)

private def pairVector (q : Fin r → V) (i j : Fin r) : Fin r → V :=
  fun k => (if k = i then q j else 0) - (if k = j then q i else 0)

private theorem pairVector_mem (q : Fin r → V) (i j : Fin r) :
    pairVector q i j ∈ Submodule.span K (Set.range (koszulVector q)) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
  · subst j
    have hzero : pairVector q i i = 0 := by ext k; simp [pairVector]
    rw [hzero]
    exact Submodule.zero_mem _
  · have heq : pairVector q i j = -koszulVector q ⟨(j, i), hij⟩ := by
      ext k
      simp only [pairVector, koszulVector, Pi.neg_apply, neg_sub]
    rw [heq]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨⟨(j, i), hij⟩, rfl⟩)

/-- There are no formal quadratic relations besides alternating constant boundaries. -/
theorem ker_formalCoefficientMap (htwo : (2 : K) ≠ 0)
    (q : Fin r → V) (hq : LinearIndependent K q) :
    LinearMap.ker (formalCoefficientMap (K := K) q) =
      Submodule.span K (Set.range (koszulVector q)) := by
  classical
  apply le_antisymm
  · intro a ha
    change formalCoefficientMap q a = 0 at ha
    obtain ⟨dual, hdual⟩ := exists_coordinate_functionals q hq
    have hrel (i : Fin r) : a i + ∑ j, dual i (a j) • q j = 0 := by
      have h := congrArg (symmetricContraction (dual i)) ha
      simpa [Finset.sum_add_distrib, hdual] using h
    have hskew (i j : Fin r) : dual j (a i) = -dual i (a j) := by
      have h := congrArg (dual j) (hrel i)
      have hij : dual j (a i) + dual i (a j) = 0 := by
        simpa [hdual, smul_eq_mul] using h
      exact eq_neg_of_add_eq_zero_left hij
    have hsum : (∑ i, ∑ j, dual j (a i) • pairVector q i j) = (2 : K) • a := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, pairVector, smul_sub,
        smul_ite, smul_zero, Finset.sum_sub_distrib]
      have hf : (∑ i, ∑ j, if k = i then dual j (a i) • q j else 0) =
          ∑ j, dual j (a k) • q j := by
        rw [Finset.sum_comm]
        simp
      have hs : (∑ i, ∑ j, if k = j then dual j (a i) • q i else 0) =
          ∑ i, dual k (a i) • q i := by simp
      rw [hf, hs]
      simp_rw [hskew k, neg_smul]
      rw [Finset.sum_neg_distrib]
      have hr : (∑ j, dual k (a j) • q j) = -a k := by
        exact eq_neg_of_add_eq_zero_right (hrel k)
      rw [hr]
      simp [two_smul]
    apply (Submodule.smul_mem_iff _ htwo).mp
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (pairVector_mem q i j)
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact formalCoefficientMap_koszul q p

/-- The image of formal coefficient multiplication is precisely the mixed-product space. -/
theorem range_formalCoefficientMap (q : Fin r → V) :
    LinearMap.range (formalCoefficientMap (K := K) q) =
      formalMixed (Submodule.span K (Set.range q)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    rw [formalCoefficientMap_apply]
    exact Submodule.sum_mem _ (fun i _ =>
      symProd_mem_formalMixed (Submodule.span K (Set.range q)) (Submodule.subset_span ⟨i, rfl⟩) (a i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, b, ha, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ha
    refine ⟨fun i => c i • b, ?_⟩
    rw [formalCoefficientMap_apply]
    change (∑ i, symProd (q i) (c i • b)) =
      (symProdLeft (K := K) b) (∑ i, c i • q i)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change symProd (q i) (c i • b) = c i • symProd (q i) b
    rw [symProd_comm (q i) (c i • b), symProd_comm (q i) b]
    exact (symProdLeft (K := K) (q i)).map_smul (c i) b

/-- Formal mixed-product spaces increase with their generator subspace. -/
theorem formalMixed_mono {L L' : Submodule K V} (h : L ≤ L') :
    formalMixed L ≤ formalMixed L' := by
  apply Submodule.span_mono
  rintro _ ⟨a, b, ha, rfl⟩
  exact ⟨a, b, h ha, rfl⟩

/-- First isomorphism theorem with an explicitly named boundary subspace. -/
def kernelModuloEquivRange {E T Z : Type*}
    [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]
    [AddCommGroup Z] [Module K Z]
    (m : E →ₗ[K] T) (B : Submodule K E) (f : m.ker →ₗ[K] Z)
    (hf : f.ker = kernelBoundary m B) : KernelModulo m B ≃ₗ[K] f.range :=
  (Submodule.quotEquivOfEq _ _ hf.symm).trans f.quotKerEquivRange

section PolynomialHomology
variable {n d : ℕ}

private def polynomialProductBilinear :
    Forms K n d →ₗ[K] Forms K n d →ₗ[K] Forms K n (2 * d) where
  toFun := mulForm
  map_add' f g := by
    apply LinearMap.ext
    intro a
    exact Subtype.ext (add_mul f.val g.val a.val)
  map_smul' c f := by
    apply LinearMap.ext
    intro a
    exact Subtype.ext (smul_mul_assoc c f.val a.val)

/-- Polynomial multiplication descended from the formal symmetric square. -/
def formalPolynomialMultiplication :
    SymmetricSquare K (Forms K n d) →ₗ[K] Forms K n (2 * d) :=
  symmetricBilinearLift polynomialProductBilinear
    (by intro a b; exact Subtype.ext (mul_comm a.val b.val))

@[simp] theorem formalPolynomialMultiplication_symProd (a b : Forms K n d) :
    formalPolynomialMultiplication (symProd a b) = mulForm a b :=
  symmetricBilinearLift_symProd _ _ a b

/-- The two multiplications factor exactly, on genuine homogeneous polynomials. -/
theorem formalPolynomialMultiplication_comp (q : Fin r → Forms K n d) :
    formalPolynomialMultiplication.comp (formalCoefficientMap q) = endpointMultiplication q := by
  ext a
  simp only [LinearMap.comp_apply, formalCoefficientMap_apply, map_sum,
    formalPolynomialMultiplication_symProd, endpointMultiplication,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- An actual endpoint cycle determines its formal symmetric relation. -/
def cycleToFormal (q : Fin r → Forms K n d) :
    (endpointMultiplication q).ker →ₗ[K] SymmetricSquare K (Forms K n d) :=
  (formalCoefficientMap q).comp (endpointMultiplication q).ker.subtype

/-- Exactly the constant Koszul boundaries map to zero. -/
theorem ker_cycleToFormal (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    LinearMap.ker (cycleToFormal q) = incomingInKernel q := by
  rw [cycleToFormal, LinearMap.ker_comp, ker_formalCoefficientMap htwo q hq]
  rfl

/-- The formal relations realized by cycles are the intersection appearing in the paper. -/
theorem range_cycleToFormal (q : Fin r → Forms K n d) :
    LinearMap.range (cycleToFormal q) =
      LinearMap.ker (formalPolynomialMultiplication (K := K) (n := n) (d := d)) ⊓
        formalMixed (Submodule.span K (Set.range q)) := by
  rw [← range_formalCoefficientMap q]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ⟨a.val, rfl⟩⟩
    change formalPolynomialMultiplication (formalCoefficientMap q a.val) = 0
    have h := LinearMap.congr_fun (formalPolynomialMultiplication_comp q) a.val
    exact h.trans a.property
  · rintro ⟨hy, ⟨a, rfl⟩⟩
    have ha : endpointMultiplication q a = 0 := by
      rw [← formalPolynomialMultiplication_comp q]
      exact hy
    exact ⟨⟨a, ha⟩, rfl⟩

/-- The actual endpoint Koszul homology is naturally the formal-product relation space. -/
def endpointHomologyEquivFormal (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    EndpointHomology q ≃ₗ[K]
      (LinearMap.ker (formalPolynomialMultiplication (K := K) (n := n) (d := d)) ⊓
        formalMixed (Submodule.span K (Set.range q)) :
          Submodule K (SymmetricSquare K (Forms K n d))) := by
  let ψ : (endpointMultiplication q).ker →ₗ[K] SymmetricSquare K (Forms K n d) :=
    cycleToFormal q
  have hψ : ψ.ker = kernelBoundary (endpointMultiplication q) (koszulSpace q) :=
    ker_cycleToFormal htwo q hq
  let e := kernelModuloEquivRange (K := K) (E := Fin r → Forms K n d)
    (T := Forms K n (2 * d)) (Z := SymmetricSquare K (Forms K n d))
    (endpointMultiplication q) (koszulSpace q) ψ hψ
  exact e.trans (LinearEquiv.ofEq _ _ (range_cycleToFormal q))

/-- In particular the two actual homology constructions have identical dimensions. -/
theorem finrank_endpointHomology_eq_formal (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    finrank K (EndpointHomology q) =
      finrank K (LinearMap.ker (formalPolynomialMultiplication (K := K) (n := n) (d := d)) ⊓
        formalMixed (Submodule.span K (Set.range q)) :
          Submodule K (SymmetricSquare K (Forms K n d))) :=
  (endpointHomologyEquivFormal htwo q hq).finrank_eq

/-- Actual first homology injects under inclusion of independent generator spaces. -/
def endpointHomologyInclusion {r' : ℕ} (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (q' : Fin r' → Forms K n d)
    (hq : LinearIndependent K q) (hq' : LinearIndependent K q')
    (hspan : Submodule.span K (Set.range q) ≤ Submodule.span K (Set.range q')) :
    EndpointHomology q →ₗ[K] EndpointHomology q' :=
  (endpointHomologyEquivFormal htwo q' hq').symm.toLinearMap.comp
    ((Submodule.inclusion (inf_le_inf le_rfl (formalMixed_mono hspan))).comp
      (endpointHomologyEquivFormal htwo q hq).toLinearMap)

theorem endpointHomologyInclusion_injective {r' : ℕ} (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (q' : Fin r' → Forms K n d)
    (hq : LinearIndependent K q) (hq' : LinearIndependent K q')
    (hspan : Submodule.span K (Set.range q) ≤ Submodule.span K (Set.range q')) :
    Function.Injective (endpointHomologyInclusion htwo q q' hq hq' hspan) :=
  (endpointHomologyEquivFormal htwo q' hq').symm.injective.comp
    ((Submodule.inclusion_injective (inf_le_inf le_rfl (formalMixed_mono hspan))).comp
      (endpointHomologyEquivFormal htwo q hq).injective)

/-- Dimension monotonicity for the genuine endpoint homology of independent tuples. -/
theorem endpointHomology_mono {r' : ℕ} (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (q' : Fin r' → Forms K n d)
    (hq : LinearIndependent K q) (hq' : LinearIndependent K q')
    (hspan : Submodule.span K (Set.range q) ≤ Submodule.span K (Set.range q')) :
    finrank K (EndpointHomology q) ≤ finrank K (EndpointHomology q') :=
  LinearMap.finrank_le_finrank_of_injective
    (endpointHomologyInclusion_injective htwo q q' hq hq' hspan)

/-- Selecting any subtuple, including a prefix, cannot increase endpoint homology. -/
theorem endpointHomology_comp_le {r' : ℕ} (htwo : (2 : K) ≠ 0)
    (q : Fin r' → Forms K n d) (hq : LinearIndependent K q) (ι : Fin r ↪ Fin r') :
    finrank K (EndpointHomology (q ∘ ι)) ≤ finrank K (EndpointHomology q) := by
  apply endpointHomology_mono htwo (q ∘ ι) q (hq.comp ι ι.injective) hq
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨ι i, rfl⟩

end PolynomialHomology
end Froberg
