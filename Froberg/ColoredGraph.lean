import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# The finite colored graphs of Appendix A.3

Subsets of the eight canonical indices are encoded by their binary masks.
A product target is encoded by its indices of positive exponent and of exponent two.
The checker reconstructs the source vertices, checks both factors of every matched
product, and checks distinctness of the resulting target monomials.
-/
namespace Froberg.ColoredGraph

structure Pattern where
  doubled : ℕ
  doubledFirstColor : ℕ
  singleFirstColor : ℕ
  degree : ℕ
  deriving DecidableEq, Repr

structure Label where
  support : ℕ
  degree : ℕ
  deriving DecidableEq, Repr

abbrev Source := Label × Label

structure Entry where
  left : Label
  right : Label
  firstFactor : ℕ
  secondFactor : ℕ
  deriving DecidableEq, Repr

def pop (mask : ℕ) : ℕ := ((List.range 8).filter mask.testBit).length

def doubledMask (p : Pattern) : ℕ := 2 ^ p.doubled - 1

def fullMask (p : Pattern) : ℕ := 2 ^ (8 - p.doubled) - 1

def colorMask (p : Pattern) : ℕ :=
  (2 ^ p.doubledFirstColor - 1) |||
    ((2 ^ p.singleFirstColor - 1) * 2 ^ p.doubled)

def labelAllowed (p : Pattern) (S b : ℕ) : Bool :=
  b == 2 || (b == 1 && pop (S &&& colorMask p) == 2) ||
    (b == 3 && pop (S &&& colorMask p) == 1)

/-- The source list is reconstructed independently of the certificate. -/
def sources (p : Pattern) : List Source :=
  (List.range 256).flatMap fun S =>
    if S < 2 ^ (8 - p.doubled) && pop S == 4 &&
        S &&& doubledMask p == doubledMask p then
      [1, 2, 3].flatMap fun b =>
        let T := (fullMask p ^^^ S) ||| doubledMask p
        let c := p.degree - b
        if b ≤ p.degree && labelAllowed p S b && labelAllowed p T c &&
            4 * S + b ≤ 4 * T + c then
          [(⟨S, b⟩, ⟨T, c⟩)]
        else []
    else []

def Entry.source (e : Entry) : Source := (e.left, e.right)

/-- The pair records all exponents of the target monomial without collisions. -/
def Entry.target (e : Entry) : ℕ × ℕ :=
  (e.firstFactor ||| e.secondFactor, e.firstFactor &&& e.secondFactor)

def Entry.validFactors (e : Entry) : Prop :=
  e.firstFactor &&& e.left.support = e.firstFactor ∧
  pop e.firstFactor = e.left.degree ∧
  e.secondFactor &&& e.right.support = e.secondFactor ∧
  pop e.secondFactor = e.right.degree ∧
  (e.left = e.right → e.firstFactor = e.secondFactor)

instance (e : Entry) : Decidable e.validFactors :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- This certificate is a matching covering every source of the reconstructed graph. -/
def ValidCertificate (p : Pattern) (es : List Entry) : Prop :=
  es.map Entry.source = sources p ∧
  (∀ e ∈ es, e.validFactors) ∧
  (es.map Entry.target).Nodup

instance (p : Pattern) (es : List Entry) : Decidable (ValidCertificate p es) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- All 275 canonical patterns, including those with no source vertices. -/
def patterns : List Pattern :=
  (List.range 5).flatMap fun i =>
    (List.range (i + 1)).flatMap fun p =>
      (List.range (9 - 2 * i)).flatMap fun q =>
        ([2, 3, 4, 5, 6].map fun k => ⟨i, p, q, k⟩)

/-- A checked certificate gives valid factors for every source vertex. -/
theorem certificate_covers (p : Pattern) (es : List Entry)
    (h : ValidCertificate p es) (s : Source) (hs : s ∈ sources p) :
    ∃ e ∈ es, e.source = s ∧ e.validFactors := by
  rw [← h.1] at hs
  obtain ⟨e, he, hes⟩ := List.mem_map.mp hs
  exact ⟨e, he, hes, h.2.1 e he⟩

end Froberg.ColoredGraph
