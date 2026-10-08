import Froberg.ColoredGraph
import Froberg.PairedMonomials
import Froberg.ConsistentProductMinors

/-! Algebraic certificates for the actual colored quartic coefficient matrices. -/
noncomputable section
namespace Froberg.ColoredGraph
open PairedMonomials ProductMinors

/-- The subset represented by the eight low bits of a mask. -/
def maskSet (S : ℕ) : Finset (Fin 8) := Finset.univ.filter (fun i => S.testBit i.val)

/-- In this module `true` denotes the y variable used in Appendix A.3. -/
def factorExponent (l : Label) (U : ℕ) : (Fin 8 × Bool) →₀ ℕ :=
  pairedExponent (maskSet l.support) (maskSet U)

/-- Actual labels retain the support subset and y-degree, independently of the mask encoding. -/
abbrev SemanticLabel := Finset (Fin 8) × ℕ

def Label.semantic (l : Label) : SemanticLabel := (maskSet l.support,l.degree)

/-- The permitted monomials attached to an actual form label. -/
def coloredTerms (l : SemanticLabel) : Finset ((Fin 8 × Bool) →₀ ℕ) :=
  allowedExponents l.2 l.1

/-- A computable coordinate vector for the selected actual monomial. -/
def factorCoordinates (l : Label) (U : ℕ) (z : Fin 8 × Bool) : ℕ :=
  if l.support.testBit z.1.val then
    if z.2 then (if U.testBit z.1.val then 1 else 0)
    else (if U.testBit z.1.val then 0 else 1)
  else 0

theorem factorExponent_apply (l : Label) (U : ℕ) (z : Fin 8 × Bool) :
    factorExponent l U z = factorCoordinates l U z := by
  rcases z with ⟨i,b⟩
  cases b <;> simp [factorExponent,pairedExponent_false,pairedExponent_true,
    maskSet,factorCoordinates] <;> split_ifs <;> simp_all

@[simp] theorem coe_factorExponent (l : Label) (U : ℕ) :
    (fun z => factorExponent l U z) = factorCoordinates l U :=
  funext (factorExponent_apply l U)

def Entry.factorChoices (e : Entry) : List (SemanticLabel × ((Fin 8 × Bool) → ℕ)) :=
  [(e.left.semantic, factorCoordinates e.left e.firstFactor),
   (e.right.semantic, factorCoordinates e.right e.secondFactor)]

def Entry.productExponent (e : Entry) : (Fin 8 × Bool) →₀ ℕ :=
  factorExponent e.left e.firstFactor + factorExponent e.right e.secondFactor

def Entry.productCoordinates (e : Entry) : (Fin 8 × Bool) → ℕ :=
  factorCoordinates e.left e.firstFactor + factorCoordinates e.right e.secondFactor

/-- A computable check of the allowed monomial conditions. -/
def allowedFactor (l : Label) (U : ℕ) : Prop :=
  maskSet U ⊆ maskSet l.support ∧ (maskSet U).card = l.degree

instance (l : Label) (U : ℕ) : Decidable (allowedFactor l U) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The check uses finite coordinate arrays, with their equality to the actual
monomial exponents proved above, so every data assertion is kernel-computable. -/
def AlgebraicCertificate (es : List Entry) : Prop :=
  (∀ e ∈ es, allowedFactor e.left e.firstFactor ∧ allowedFactor e.right e.secondFactor) ∧
  (∀ p ∈ es.flatMap Entry.factorChoices, ∀ q ∈ es.flatMap Entry.factorChoices,
    p.1 = q.1 → p.2 = q.2) ∧
  (es.map Entry.productCoordinates).Nodup

instance (es : List Entry) : Decidable (AlgebraicCertificate es) :=
  inferInstanceAs (Decidable (_ ∧ _))

def entryLabel (es : List Entry) (p : Fin es.length × Bool) : SemanticLabel :=
  if p.2 then es[p.1].right.semantic else es[p.1].left.semantic

def entryChoice (es : List Entry) (p : Fin es.length × Bool) : (Fin 8 × Bool) →₀ ℕ :=
  if p.2 then factorExponent es[p.1].right es[p.1].secondFactor
    else factorExponent es[p.1].left es[p.1].firstFactor

private theorem entryChoice_mem (es : List Entry) (p : Fin es.length × Bool) :
    (entryLabel es p, fun z => entryChoice es p z) ∈ es.flatMap Entry.factorChoices := by
  apply List.mem_flatMap.mpr
  refine ⟨es[p.1],List.getElem_mem p.1.isLt,?_⟩
  cases p with | mk i b =>
    cases b <;> simp [entryLabel,entryChoice,Entry.factorChoices,coe_factorExponent]

/-- Every algebraic certificate proves a nonzero minor of the genuine generic
colored polynomial products. This does not replace multiplication by a formal matrix. -/
theorem algebraicCertificate_minor {K : Type*} [CommRing K] [Nontrivial K]
    (es : List Entry) (h : AlgebraicCertificate es) :
    (productMinor (K := K) coloredTerms (fun i : Fin es.length => es[i].left.semantic)
      (fun i : Fin es.length => es[i].right.semantic)
      (fun i : Fin es.length => es[i].productExponent)).det ≠ 0 := by
  have hc : (entryChoice es).FactorsThrough (entryLabel es) := by
    intro p q hpq
    apply Finsupp.ext
    exact congrFun (h.2.1 _ (entryChoice_mem es p) _ (entryChoice_mem es q) hpq)
  have hm : ∀ p, entryChoice es p ∈ coloredTerms (entryLabel es p) := by
    rintro ⟨i,b⟩
    have hi := h.1 es[i] (List.getElem_mem i.isLt)
    cases b
    · exact mem_allowedExponents hi.1.1 hi.1.2
    · exact mem_allowedExponents hi.2.1 hi.2.2
  have hinj : Function.Injective (fun i : Fin es.length =>
      entryChoice es (i,false) + entryChoice es (i,true)) := by
    intro i j hij
    have hg : Function.Injective (es.map Entry.productCoordinates).get :=
      List.nodup_iff_injective_get.mp h.2.2
    have he : (es.map Entry.productCoordinates).get ⟨i.val,by simpa using i.isLt⟩ =
        (es.map Entry.productCoordinates).get ⟨j.val,by simpa using j.isLt⟩ := by
      have he := congrArg (fun x : (Fin 8 × Bool) →₀ ℕ => (fun z => x z)) hij
      apply funext
      intro z
      simpa [entryChoice,Entry.productCoordinates,factorExponent_apply] using congrFun he z
    have hv := congrArg Fin.val (hg he)
    exact Fin.ext hv
  simpa only [entryLabel,entryChoice,Bool.false_eq_true,reduceIte,Entry.productExponent] using
    consistent_productMinor_ne_zero (K := K) coloredTerms (entryLabel es) (entryChoice es) hc hm hinj

end Froberg.ColoredGraph
