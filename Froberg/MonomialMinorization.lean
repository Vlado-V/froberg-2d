import Froberg.MonomialMixing
import Froberg.EmbeddedMinorization
import Froberg.ProfileTotalLimits

/-! The common-target estimate yields a minorization by a probability
measure on the actual all-free source monomials. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

def freeSourceEmbedding {a z s : ℕ} (hs : 0 < s) :
    Degree z s ↪ Σ i, SourceMonomialFiber a z s i where
  toFun := freeSource hs
  inj' := by
    intro γ δ h
    apply Subtype.ext
    exact congrArg (fun α : Σ i, SourceMonomialFiber a z s i => α.2.2.val) h

lemma degree_nonempty {z : ℕ} (hz : 0 < z) (s : ℕ) : Nonempty (Degree z s) := by
  apply Fintype.card_pos_iff.mp
  rw [card_degree]
  exact Nat.choose_pos (by omega)

lemma sourceAtomMass_upper {H : ℝ} {a z s : ℕ}
    (hA : 0 < ∑ i, finiteSourceProfile H s a z i) (i : Option (Fin s)) :
    sourceAtomMass H s a z i ≤ H / (∑ k, finiteSourceProfile H s a z k) := by
  apply div_le_div_of_nonneg_right _ hA.le
  cases i <;> simp [profileSourceCapacity]

theorem monomial_minorization {a z s : ℕ} {H : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hs : 0 < s) (hH : 0 < H)
    (hA : 0 < ∑ i, finiteSourceProfile H s a z i)
    (P : Option (Fin s) → Fin (2*s+1) → ℝ) (q : Fin (2*s+1) → ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hq : ∀ j, 0 < q j ∧ q j ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ i j, profileAllowed i j → ε ≤ P i j) :
    ∀ α γ : Σ i, SourceMonomialFiber a z s i,
      monomialMixingCoefficient s a z H ε * sourceAtomMass H s a z α.1 *
          embeddedUniform (freeSourceEmbedding hs) γ ≤
        reversibleWeights
          (fun β : Σ j, TargetMonomialFiber a z s j => q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ))
          (jointConditional (monomialProfileJoint P)
            (fun β => q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ))) α γ := by
  letI := degree_nonempty hz s
  let ν := fun β : Σ j, TargetMonomialFiber a z s j =>
    q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ)
  let C := jointConditional (monomialProfileJoint P) ν
  let B := (z : ℝ) * ε^2 /
    (((a+z+(2*s+1)-1).choose (2*s+1) : ℝ) * (2^(2*s+1))^2)
  let M := H / (∑ i, finiteSourceProfile H s a z i)
  have hν (β : Σ j, TargetMonomialFiber a z s j) : 0 ≤ ν β := by
    exact div_nonneg (hq β.1).1.le (Nat.cast_nonneg _)
  have hC (β : Σ j, TargetMonomialFiber a z s j) (α : Σ i, SourceMonomialFiber a z s i) : 0 ≤ C β α :=
    jointConditional_nonneg _ _ (monomialProfileJoint_nonneg P hP0) hν β α
  have hW (α γ : Σ i, SourceMonomialFiber a z s i) : 0 ≤ reversibleWeights ν C α γ := by
    exact sum_nonneg fun β _ => mul_nonneg (mul_nonneg (hν β) (hC β α)) (hC β γ)
  have hh := embedded_family_minorization (freeSourceEmbedding (a := a) (z := z) hs)
    (reversibleWeights ν C) (fun α => sourceAtomMass H s a z α.1) B M
    (by dsimp [B]; positivity) (div_pos hH hA) hW
    (fun α => sourceAtomMass_upper hA α.1)
    (fun α γ => monomialProfile_reversible_minorization ha hz hs P q hP0 hq ε hε hP α γ)
  have he : B * Fintype.card (Degree z s) / M = monomialMixingCoefficient s a z H ε := by
    dsimp [B, M, monomialMixingCoefficient]
    rw [card_degree]
    field_simp
    <;> ring
  rwa [he] at hh

end Froberg
