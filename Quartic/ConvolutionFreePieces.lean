import Quartic.FreePieces
import Quartic.ConvolutionFree
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Decomposing the actual free polynomial extension of the convolution quotient

The decomposition is induced by free-monomial coefficient extraction on the
polynomial presentation itself. In particular it is compatible with the
relations, not just an equality of the dimensions of abstract vector spaces.
-/

noncomputable section
namespace Quartic.ConvolutionFreePieces
open MvPolynomial FreeCoefficients ConvolutionPresentation
variable {K : Type*} [Field K] {t w d j : ℕ}

abbrev PolySource (K : Type*) [Field K] (t w : ℕ) :=
  Fin (t + 2) → Quartic.Poly K (t + w)
abbrev PolyTarget (K : Type*) [Field K] (t w : ℕ) :=
  Fin 3 → Quartic.Poly K (t + w)

/-- The same convolution columns acting on arbitrary polynomial coefficients. -/
def polyPresentation : PolySource K t w →ₗ[K] PolyTarget K t w where
  toFun a r := ∑ i : Fin t, X (Fin.castAdd w i) * a (columnIndex r i)
  map_add' a b := by funext r; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by funext r; simp [Finset.smul_sum]

@[simp] theorem polyPresentation_apply (a : PolySource K t w) (r : Fin 3) :
    polyPresentation a r = ∑ i : Fin t, X (Fin.castAdd w i) * a (columnIndex r i) := rfl

/-- Forget the homogeneous degree in each output row. -/
def targetInclusion : ConvolutionFree.Target K t w d →ₗ[K] PolyTarget K t w :=
  LinearMap.pi fun r => (Quartic.Forms K (t + w) d).subtype.comp (LinearMap.proj r)

@[simp] theorem targetInclusion_apply (v : ConvolutionFree.Target K t w d) (r : Fin 3) :
    targetInclusion v r = (v r).val := rfl

/-- The homogeneous part of the relations of the polynomial presentation. -/
def relations (K : Type*) [Field K] (t w d : ℕ) :
    Submodule K (ConvolutionFree.Target K t w d) :=
  (LinearMap.range (polyPresentation (K := K) (t := t) (w := w))).comap targetInclusion

theorem mem_relations_iff (v : ConvolutionFree.Target K t w d) :
    v ∈ relations K t w d ↔ ∃ a : PolySource K t w, polyPresentation a = targetInclusion v :=
  Iff.rfl

/-- Free coefficients commute with the actual full polynomial presentation. -/
theorem polyPresentation_freeCoeff (b : Fin w →₀ ℕ) (a : PolySource K t w) (r : Fin 3) :
    freeCoeff b (polyPresentation a r) =
      polyPresentation (w := 0) (fun k => freeCoeff b (a k)) r := by
  simp only [polyPresentation_apply, map_sum, freeCoeff_core_X_mul]
  rfl

/-- Inserting a free monomial commutes with the actual polynomial presentation. -/
theorem polyPresentation_liftCoeff (b : Fin w →₀ ℕ) (a : PolySource K t 0) (r : Fin 3) :
    polyPresentation (fun k => liftCoeff b (a k)) r =
      liftCoeff b (polyPresentation a r) := by
  simp only [polyPresentation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (liftCoeff_core_X_mul b (a (columnIndex r i)) i).symm

abbrev TargetPieces (K : Type*) [Field K] (t w d : ℕ) :=
  ∀ b : BoundedExponent w d, ConvolutionFree.Target K t 0 (d - b.val.degree)

/-- Split each output row, then group the rows with the same free monomial. -/
def targetPiecesEquiv : ConvolutionFree.Target K t w d ≃ₗ[K] TargetPieces K t w d where
  toFun v b r := split (v r) b
  invFun v r := join (fun b => v b r)
  left_inv v := by funext r; exact join_split (v r)
  right_inv v := by funext b r; exact congrFun (split_join (fun e => v e r)) b
  map_add' v z := by ext b r; simp
  map_smul' c v := by ext b r; simp

@[simp] theorem targetPiecesEquiv_apply_val (v : ConvolutionFree.Target K t w d)
    (b : BoundedExponent w d) (r : Fin 3) :
    (targetPiecesEquiv v b r).val = freeCoeff b.val (v r).val := rfl

@[simp] theorem targetPiecesEquiv_symm_apply_val (v : TargetPieces K t w d) (r : Fin 3) :
    (targetPiecesEquiv.symm v r).val =
      ∑ b : BoundedExponent w d, liftCoeff b.val (v b r).val := join_apply_val _

/-- Every coefficient of an extended relation is a core relation. -/
theorem relation_coeff (v : ConvolutionFree.Target K t w d) (hv : v ∈ relations K t w d)
    (b : BoundedExponent w d) :
    targetPiecesEquiv v b ∈ relations K t 0 (d - b.val.degree) := by
  obtain ⟨a, ha⟩ := (mem_relations_iff v).mp hv
  refine ⟨fun k => freeCoeff b.val (a k), ?_⟩
  funext r
  rw [← polyPresentation_freeCoeff, ha]
  rfl

/-- Conversely all the core coefficient relations reconstruct an extended relation. -/
theorem relation_join (v : TargetPieces K t w d)
    (hv : ∀ b, v b ∈ relations K t 0 (d - b.val.degree)) :
    targetPiecesEquiv.symm v ∈ relations K t w d := by
  classical
  choose a ha using fun b => (mem_relations_iff (v b)).mp (hv b)
  refine ⟨fun k => ∑ b, liftCoeff b.val (a b k), ?_⟩
  funext r
  change (∑ i : Fin t, X (Fin.castAdd w i) * ∑ b, liftCoeff b.val (a b (columnIndex r i))) = _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ b, polyPresentation (fun k => liftCoeff b.val (a b k)) r) = _
  simp only [polyPresentation_liftCoeff, ha, targetInclusion_apply,
    targetPiecesEquiv_symm_apply_val]

/-- Under the coefficient equivalence, relations split independently by free monomial. -/
theorem map_relations :
    (relations K t w d).map targetPiecesEquiv.toLinearMap =
      Submodule.pi Set.univ (fun b : BoundedExponent w d =>
        relations K t 0 (d - b.val.degree)) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩ b _
    exact relation_coeff z hz b
  · intro hv
    refine ⟨targetPiecesEquiv.symm v, relation_join v (fun b => hv b (Set.mem_univ b)), ?_⟩
    exact targetPiecesEquiv.apply_symm_apply v

/-- The actual homogeneous polynomial-extension quotient, in every degree. -/
abbrev Piece (K : Type*) [Field K] (t w d : ℕ) :=
  ConvolutionFree.Target K t w d ⧸ relations K t w d

/-- Canonical decomposition of the actual quotient by its free-monomial factors. -/
def quotientPiecesEquiv : Piece K t w d ≃ₗ[K]
    ∀ b : BoundedExponent w d, Piece K t 0 (d - b.val.degree) := by
  classical
  exact (Submodule.Quotient.equiv _ _ targetPiecesEquiv map_relations).trans
    (Submodule.quotientPi _)

/-- Extracting the next homogeneous degree commutes with multiplication by a variable. -/
theorem homogeneousComponent_X_mul (i : Fin t) (p : Quartic.Poly K t) (j : ℕ) :
    homogeneousComponent (j + 1) (X i * p) = X i * homogeneousComponent j p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      simp only [MvPolynomial.X, monomial_mul_monomial, one_mul]
      rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl),
        homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
      have h : j + 1 = (Finsupp.single i 1 + a).degree ↔ j = a.degree := by
        simp only [map_add, Finsupp.degree_single]
        omega
      simp only [h]
      split_ifs <;> simp [monomial_mul_monomial]
  | add p q hp hq => simp [mul_add, hp, hq]

/-- The homogeneous relations agree exactly with the previously defined graded presentation. -/
theorem relations_succ : relations K t w (j + 1) =
    LinearMap.range (ConvolutionFree.presentation (K := K) (t := t) (w := w) (j := j)) := by
  ext v
  constructor
  · rintro ⟨a, ha⟩
    let a' : ConvolutionFree.Source K t w j := fun k =>
      ⟨homogeneousComponent j (a k), homogeneousComponent_isHomogeneous j (a k)⟩
    refine ⟨a', ?_⟩
    funext r
    apply Subtype.ext
    have h := congrArg (fun z : PolyTarget K t w => homogeneousComponent (j + 1) (z r)) ha
    simp only [polyPresentation_apply, map_sum, homogeneousComponent_X_mul,
      targetInclusion_apply, homogeneousComponent_eq_self (v r).property] at h
    simpa only [ConvolutionFree.presentation_apply_val, a'] using h
  · rintro ⟨a, rfl⟩
    refine ⟨fun k => (a k).val, ?_⟩
    funext r
    simp only [polyPresentation_apply, targetInclusion_apply, ConvolutionFree.presentation_apply_val]

/-- The polynomial presentation has no relations in degree zero. -/
theorem relations_zero : relations K t w 0 = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  obtain ⟨a, ha⟩ := (mem_relations_iff v).mp hv
  funext r
  apply Subtype.ext
  have h := congrArg (fun z : PolyTarget K t w => homogeneousComponent 0 (z r)) ha
  have hz : homogeneousComponent 0 (polyPresentation a r) = 0 := by
    simp [polyPresentation_apply, homogeneousComponent_zero, coeff_X_mul']
  rw [hz, targetInclusion_apply, homogeneousComponent_eq_self (v r).property] at h
  exact h.symm

/-- Identification with the existing actual positive-degree cokernel. -/
def pieceSuccEquiv : Piece K t w (j + 1) ≃ₗ[K] ConvolutionFree.Cokernel K t w j :=
  Submodule.quotEquivOfEq _ _ relations_succ

/-- Degree zero consists of the three original output rows. -/
def pieceZeroEquiv : Piece K t w 0 ≃ₗ[K] ConvolutionFree.Target K t w 0 :=
  Submodule.quotEquivOfEqBot _ relations_zero

/-- The decomposition for the existing graded cokernel, with explicit maps in all degrees. -/
def cokernelPiecesEquiv : ConvolutionFree.Cokernel K t w j ≃ₗ[K]
    ∀ b : BoundedExponent w (j + 1), Piece K t 0 (j + 1 - b.val.degree) :=
  pieceSuccEquiv.symm.trans quotientPiecesEquiv

@[simp] theorem quotientPiecesEquiv_mk (v : ConvolutionFree.Target K t w d)
    (b : BoundedExponent w d) :
    quotientPiecesEquiv (Submodule.Quotient.mk v) b =
      Submodule.Quotient.mk (targetPiecesEquiv v b) := rfl

/-- With no free variables the graded presentation is exactly the core presentation. -/
theorem core_presentation_eq :
    ConvolutionFree.presentation (K := K) (t := t) (w := 0) (j := j) =
      ConvolutionPresentation.presentation (K := K) (t := t) (j := j) := by
  apply LinearMap.ext
  intro a
  funext r
  apply Subtype.ext
  simp only [ConvolutionFree.presentation_apply_val, ConvolutionPresentation.presentation_apply_val]
  rfl

/-- The core positive-degree component is the original convolution cokernel. -/
def corePieceSuccEquiv : Piece K t 0 (j + 1) ≃ₗ[K] ConvolutionPresentation.Cokernel K t j :=
  pieceSuccEquiv.trans (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range core_presentation_eq))

/-- The core relation space fills every output of degree at least three. -/
theorem coreRelations_eq_top (hd : 3 ≤ d) : relations K t 0 d = ⊤ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [relations_succ, core_presentation_eq]
  exact LinearMap.range_eq_top.mpr (ConvolutionInverse.presentation_surjective_of_three_le hd)

/-- Only core degrees zero, one and two can survive in the free-variable decomposition. -/
theorem corePiece_eq_zero (hd : 3 ≤ d) (x : Piece K t 0 d) : x = 0 := by
  have : Subsingleton (Piece K t 0 d) :=
    Submodule.Quotient.subsingleton_iff.mpr (coreRelations_eq_top hd)
  exact Subsingleton.elim _ _

/-- In the canonical decomposition all higher-core-degree coordinates are zero. -/
theorem quotientPiecesEquiv_high_core (x : Piece K t w d) (b : BoundedExponent w d)
    (hb : 3 ≤ d - b.val.degree) : quotientPiecesEquiv x b = 0 :=
  corePiece_eq_zero hb _

theorem corePieceZero_finrank : Module.finrank K (Piece K t 0 0) = 3 := by
  rw [pieceZeroEquiv.finrank_eq]
  exact degreeZero_finrank

theorem corePieceOne_finrank (ht : 2 ≤ t) :
    Module.finrank K (Piece K t 0 1) = 2 * (t - 1) := by
  rw [(corePieceSuccEquiv (K := K) (t := t) (j := 0)).finrank_eq]
  exact cokernel_degreeOne_finrank (by omega)

theorem corePieceTwo_finrank (ht : 2 ≤ t) :
    Module.finrank K (Piece K t 0 2) = t.choose 2 := by
  rw [(corePieceSuccEquiv (K := K) (t := t) (j := 1)).finrank_eq]
  exact ConvolutionHilbert.cokernel_degreeTwo_finrank ht

end Quartic.ConvolutionFreePieces
