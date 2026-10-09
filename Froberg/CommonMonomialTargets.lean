module

public import Froberg.MonomialProfileTransport

@[expose] public section

/-! Distinct common targets connecting every source monomial to every
all-free source monomial. No variable needs to be outside the supports. -/
noncomputable section
namespace Froberg
open MonomialExpansion

/-- The all-free degree-s monomial as an individual source state. -/
def freeSource {a z s : ℕ} (hs : 0 < s) (γ : Degree z s) :
    Σ i, SourceMonomialFiber a z s i :=
  ⟨some ⟨0, hs⟩, ⟨0, by simp [mem_exponents, profileSourceIndex]⟩, γ⟩

def commonTargetIndex {s : ℕ} (i : Option (Fin s)) : Fin (2 * s + 1) :=
  ⟨profileSourceIndex i, by have hi := profileSourceIndex_le i; omega⟩

/-- Multiplying the two source monomials and one free variable. -/
def commonTarget {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i)
    (γ : Degree z s) (t : Fin z) : Σ j, TargetMonomialFiber a z s j :=
  ⟨commonTargetIndex α.1, α.2.1,
    ⟨α.2.2.val + γ.val + Finsupp.single t 1, mem_exponents.mpr (by
      simp only [map_add, degree_val, Finsupp.degree_single, commonTargetIndex]
      have hi := profileSourceIndex_le α.1
      omega)⟩⟩

lemma commonTarget_injective {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i)
    (γ : Degree z s) : Function.Injective (commonTarget α γ) := by
  intro t u h
  have hf := congrArg (fun β : Σ j, TargetMonomialFiber a z s j => β.2.2.val) h
  change α.2.2.val + γ.val + Finsupp.single t 1 =
    α.2.2.val + γ.val + Finsupp.single u 1 at hf
  exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) (add_left_cancel hf)

def commonTargetEmbedding {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i)
    (γ : Degree z s) : Fin z ↪ Σ j, TargetMonomialFiber a z s j :=
  ⟨commonTarget α γ, commonTarget_injective α γ⟩

lemma commonTarget_allowed_left {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i)
    (γ : Degree z s) (t : Fin z) : profileAllowed α.1 (commonTarget α γ t).1 := by
  simp only [commonTarget, commonTargetIndex, profileAllowed]
  omega

lemma commonTarget_allowed_free {a z s : ℕ} (hs : 0 < s)
    (α : Σ i, SourceMonomialFiber a z s i) (γ : Degree z s) (t : Fin z) :
    profileAllowed (freeSource (a := a) hs γ).1 (commonTarget α γ t).1 := by
  have hi := profileSourceIndex_le α.1
  change 0 ≤ profileSourceIndex α.1 ∧ profileSourceIndex α.1 ≤ 0 + s + 1
  constructor <;> omega

lemma commonTarget_divides_left {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i)
    (γ : Degree z s) (t : Fin z) :
    OuterInjection.joinParts α.2.1.val α.2.2.val ≤
      OuterInjection.joinParts (commonTarget α γ t).2.1.val (commonTarget α γ t).2.2.val := by
  rw [OuterInjection.joinParts_le_joinParts]
  exact ⟨le_rfl, le_self_add.trans le_self_add⟩

lemma commonTarget_divides_free {a z s : ℕ} (hs : 0 < s)
    (α : Σ i, SourceMonomialFiber a z s i) (γ : Degree z s) (t : Fin z) :
    OuterInjection.joinParts (freeSource (a := a) hs γ).2.1.val (freeSource (a := a) hs γ).2.2.val ≤
      OuterInjection.joinParts (commonTarget α γ t).2.1.val (commonTarget α γ t).2.2.val := by
  rw [OuterInjection.joinParts_le_joinParts]
  exact ⟨zero_le, le_add_self.trans le_self_add⟩

end Froberg
