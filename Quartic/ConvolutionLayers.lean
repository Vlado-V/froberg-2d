import Quartic.ConvolutionFreeMultiplication
import Quartic.FreeMonomialCounts

/-!
# The grouped free-variable layers of the actual convolution quotient

The coefficient decomposition is regrouped by free degree, retaining its
canonical maps. In degrees one and three this yields exactly the summands
used in the manuscript's profile argument.
-/

noncomputable section
namespace Quartic.ConvolutionLayers
open FreeCoefficients FreeMonomialCounts ConvolutionFreePieces ConvolutionFreeMultiplication
variable {K : Type*} [Field K] {t w d e : ℕ}

/-- Transport the homogeneous degree without changing the underlying class. -/
def pieceCast (h : d = e) : Piece K t w d ≃ₗ[K] Piece K t w e := by
  subst e
  exact LinearEquiv.refl _ _

@[simp] theorem pieceCast_rfl : pieceCast (K := K) (t := t) (w := w) (rfl : d = d) =
    LinearEquiv.refl _ _ := rfl

@[simp] theorem pieceCast_self (h : d = d) (x : Piece K t w d) : pieceCast h x = x := rfl

/-- The same degree transport before taking the quotient. -/
def targetCast (h : d = e) :
    ConvolutionFree.Target K t w d ≃ₗ[K] ConvolutionFree.Target K t w e := by
  subst e
  exact LinearEquiv.refl _ _

@[simp] theorem targetCast_self (h : d = d) (v : ConvolutionFree.Target K t w d) :
    targetCast h v = v := rfl

@[simp] theorem targetCast_apply_val (h : d = e) (v : ConvolutionFree.Target K t w d)
    (r : Fin 3) : (targetCast h v r).val = (v r).val := by
  subst e
  rfl

@[simp] theorem pieceCast_mk (h : d = e) (v : ConvolutionFree.Target K t w d) :
    pieceCast h (Submodule.Quotient.mk v) = Submodule.Quotient.mk (targetCast h v) := by
  subst e
  rfl

/-- Index a bounded free exponent by its exact degree and its monomial. -/
def exponentDegreeEquiv : BoundedExponent w d ≃
    Σ k : Fin (d + 1), ExactExponent w k.val where
  toFun b := ⟨⟨b.val.degree, by omega⟩, ⟨b.val, rfl⟩⟩
  invFun s := ⟨s.2.val, by rw [s.2.property]; omega⟩
  left_inv b := Subtype.ext rfl
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨b, hb⟩⟩
    dsimp
    change b.degree = k at hb
    subst k
    rfl

/-- Fixed-free-degree coefficients, in the corresponding core quotient piece. -/
abbrev Layers (K : Type*) [Field K] (t w d : ℕ) :=
  ∀ k : Fin (d + 1), ExactExponent w k.val → Piece K t 0 (d - k.val)

/-- Regroup the actual coefficient summands by their free degree. -/
def regroupPieces :
    (∀ b : BoundedExponent w d, Piece K t 0 (d - b.val.degree)) ≃ₗ[K] Layers K t w d :=
  ((LinearEquiv.piCongrLeft' K _ exponentDegreeEquiv).trans
    (LinearEquiv.piCongrRight fun s =>
      pieceCast (show d - (exponentDegreeEquiv.symm s).val.degree = d - s.1.val from by
        change d - s.2.val.degree = d - s.1.val
        rw [s.2.property]))).trans (LinearEquiv.piCurry K _)

/-- The actual quotient, decomposed by core degree and free monomial. -/
def layersEquiv : Piece K t w d ≃ₗ[K] Layers K t w d :=
  quotientPiecesEquiv.trans regroupPieces

/-- There is exactly one free monomial of degree zero. -/
def zeroExponent (w : ℕ) : ExactExponent w 0 := ⟨0, by simp⟩

theorem exactExponent_zero_unique (b : ExactExponent w 0) : b = zeroExponent w := by
  apply Subtype.ext
  exact (Finsupp.degree_eq_zero_iff b.val).mp b.property

/-- Constant families on degree-zero free monomials are the core space itself. -/
def zeroLayerEquiv (V : Type*) [AddCommGroup V] [Module K V] :
    (ExactExponent w 0 → V) ≃ₗ[K] V where
  toFun v := v (zeroExponent w)
  invFun x _ := x
  left_inv v := by funext b; rw [exactExponent_zero_unique b]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree-one free monomials are precisely the individual free variables. -/
def oneExponentEquiv : Fin w ≃ ExactExponent w 1 :=
  Sym.oneEquiv.trans (Quartic.exponentEquiv w 1)

@[simp] theorem oneExponentEquiv_val (i : Fin w) :
    (oneExponentEquiv i).val = Finsupp.single i 1 := by
  ext j
  change ({i} : Multiset (Fin w)).count j = (Finsupp.single i 1) j
  rw [Multiset.count_singleton, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- The degree-one free layer is one copy of the core space for each free variable. -/
def oneLayerEquiv (V : Type*) [AddCommGroup V] [Module K V] :
    (ExactExponent w 1 → V) ≃ₗ[K] (Fin w → V) :=
  LinearEquiv.piCongrLeft' K (fun _ => V) oneExponentEquiv.symm

/-- The actual first graded piece is the core first piece and the free output copies. -/
def degreeOneEquiv : Piece K t w 1 ≃ₗ[K]
    Piece K t 0 1 × (Fin w → Piece K t 0 0) :=
  (layersEquiv.trans (LinearEquiv.piFinTwo K _)).trans
    ((zeroLayerEquiv _).prodCongr (oneLayerEquiv _))

/-- Remove the vanishing core cubic component from the four free-degree layers. -/
def omitCoreCubic : Layers K t w 3 ≃ₗ[K]
    (ExactExponent w 1 → Piece K t 0 2) ×
      (ExactExponent w 2 → Piece K t 0 1) ×
        (ExactExponent w 3 → Piece K t 0 0) where
  toFun v := (v 1, v 2, v 3)
  invFun v := Fin.cases (fun _ => 0)
    (Fin.cases v.1 (Fin.cases v.2.1 (Fin.cases v.2.2 (fun i => Fin.elim0 i))))
  left_inv v := by
    funext k b
    fin_cases k
    · exact (corePiece_eq_zero (d := 3) (by decide) (v 0 b)).symm
    · rfl
    · rfl
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exactly the three surviving cubic layers, with individual free monomial indices. -/
def degreeThreeEquiv : Piece K t w 3 ≃ₗ[K]
    (Fin w → Piece K t 0 2) ×
      (ExactExponent w 2 → Piece K t 0 1) ×
        (ExactExponent w 3 → Piece K t 0 0) :=
  (layersEquiv.trans omitCoreCubic).trans
    ((oneLayerEquiv _).prodCongr (LinearEquiv.refl _ _))

/-- A coefficient row with its core degree written using an exact free degree. -/
def coefficientRows {k : ℕ} (b : ExactExponent w k) (v : ConvolutionFree.Target K t w d) :
    ConvolutionFree.Target K t 0 (d - k) := fun r =>
  ⟨freeCoeff b.val (v r).val, by
    change (freeCoeff b.val (v r).val).IsHomogeneous (d - k)
    simpa only [b.property] using freeCoeff_homogeneous (v r).val (v r).property b.val⟩

/-- The regrouped quotient equivalence still extracts the literal free coefficients. -/
theorem layersEquiv_mk (v : ConvolutionFree.Target K t w d) (k : Fin (d + 1))
    (b : ExactExponent w k.val) :
    layersEquiv (Submodule.Quotient.mk v) k b = Submodule.Quotient.mk (coefficientRows b v) := by
  rcases k with ⟨k, hk⟩
  rcases b with ⟨b, hb⟩
  change b.degree = k at hb
  subst k
  rfl

theorem degreeOneEquiv_mk_core (v : ConvolutionFree.Target K t w 1) :
    (degreeOneEquiv (Submodule.Quotient.mk v)).1 =
      Submodule.Quotient.mk (coefficientRows (zeroExponent w) v) := by
  exact layersEquiv_mk v 0 (zeroExponent w)

theorem degreeOneEquiv_mk_free (v : ConvolutionFree.Target K t w 1) (i : Fin w) :
    (degreeOneEquiv (Submodule.Quotient.mk v)).2 i =
      Submodule.Quotient.mk (coefficientRows (oneExponentEquiv i) v) := by
  exact layersEquiv_mk v 1 (oneExponentEquiv i)

theorem degreeThreeEquiv_mk_linear (v : ConvolutionFree.Target K t w 3) (i : Fin w) :
    (degreeThreeEquiv (Submodule.Quotient.mk v)).1 i =
      Submodule.Quotient.mk (coefficientRows (oneExponentEquiv i) v) := by
  exact layersEquiv_mk v 1 (oneExponentEquiv i)

theorem degreeThreeEquiv_mk_quadratic (v : ConvolutionFree.Target K t w 3)
    (b : ExactExponent w 2) :
    (degreeThreeEquiv (Submodule.Quotient.mk v)).2.1 b =
      Submodule.Quotient.mk (coefficientRows b v) := by
  exact layersEquiv_mk v 2 b

theorem degreeThreeEquiv_mk_cubic (v : ConvolutionFree.Target K t w 3)
    (b : ExactExponent w 3) :
    (degreeThreeEquiv (Submodule.Quotient.mk v)).2.2 b =
      Submodule.Quotient.mk (coefficientRows b v) := by
  exact layersEquiv_mk v 3 b

end Quartic.ConvolutionLayers
