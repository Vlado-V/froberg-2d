module

public import Froberg.MonomialCouplingBounds
public import Froberg.CommonMonomialTargets
public import Froberg.JointConditionals

@[expose] public section

/-! A direct quantitative mixing estimate for the lifted monomial
transport, using a full family of common free-variable targets. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

lemma targetMonomialFiber_card_le (a z s : ℕ) (j : Fin (2 * s + 1)) :
    Fintype.card (TargetMonomialFiber a z s j) ≤ (a + z + (2 * s + 1) - 1).choose (2 * s + 1) := by
  have h := Fintype.card_subtype_le
    (fun β : Degree (a + z) (2 * s + 1) => (OuterInjection.corePart β.val).degree = j.val)
  rw [OuterInjection.card_bidegree a z (2 * s + 1) j (by omega), card_degree] at h
  rwa [targetMonomialFiber_card]

lemma monomialProfileJoint_local_lower {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ i j, profileAllowed i j → ε ≤ P i j)
    (α : Σ i, SourceMonomialFiber a z s i) (β : Σ j, TargetMonomialFiber a z s j)
    (hab : profileAllowed α.1 β.1)
    (hdiv : OuterInjection.joinParts α.2.1.val α.2.2.val ≤
      OuterInjection.joinParts β.2.1.val β.2.2.val) :
    ε / ((Fintype.card (TargetMonomialFiber a z s β.1) : ℝ) * 2 ^ (2 * s + 1)) ≤
      monomialProfileJoint P α β := by
  have hlocal := localMonomialCoupling_uniform_lower ha hz α.1 β.1 hab α.2 β.2 hdiv
  calc
    _ = ε * (1 / ((Fintype.card (TargetMonomialFiber a z s β.1) : ℝ) * 2 ^ (2 * s + 1))) := by ring
    _ ≤ ε * localMonomialCoupling α.1 β.1 α.2 β.2 := mul_le_mul_of_nonneg_left hlocal hε
    _ ≤ monomialProfileJoint P α β :=
      mul_le_mul_of_nonneg_right (hP α.1 β.1 hab) (localMonomialCoupling_nonneg α.1 β.1 α.2 β.2)

lemma monomialProfileJoint_uniform_lower {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ i j, profileAllowed i j → ε ≤ P i j)
    (α : Σ i, SourceMonomialFiber a z s i) (β : Σ j, TargetMonomialFiber a z s j)
    (hab : profileAllowed α.1 β.1)
    (hdiv : OuterInjection.joinParts α.2.1.val α.2.2.val ≤
      OuterInjection.joinParts β.2.1.val β.2.2.val) :
    ε / (((a + z + (2 * s + 1) - 1).choose (2 * s + 1) : ℝ) * 2 ^ (2 * s + 1)) ≤
      monomialProfileJoint P α β := by
  apply le_trans _ (monomialProfileJoint_local_lower ha hz P ε hε hP α β hab hdiv)
  have hc : (0 : ℝ) < Fintype.card (TargetMonomialFiber a z s β.1) := by
    exact_mod_cast targetMonomialFiber_card_pos ha hz β.1
  apply div_le_div_of_nonneg_left hε (mul_pos hc (by positivity))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast targetMonomialFiber_card_le a z s β.1) (by positivity)

lemma monomialProfileConditional_uniform_lower {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (q : Fin (2 * s + 1) → ℝ)
    (hq : ∀ j, 0 < q j ∧ q j ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ i j, profileAllowed i j → ε ≤ P i j)
    (α : Σ i, SourceMonomialFiber a z s i) (β : Σ j, TargetMonomialFiber a z s j)
    (hab : profileAllowed α.1 β.1)
    (hdiv : OuterInjection.joinParts α.2.1.val α.2.2.val ≤
      OuterInjection.joinParts β.2.1.val β.2.2.val) :
    ε / 2 ^ (2 * s + 1) ≤
      jointConditional (monomialProfileJoint P)
        (fun β => q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ)) β α := by
  have hc : (0 : ℝ) < Fintype.card (TargetMonomialFiber a z s β.1) := by
    exact_mod_cast targetMonomialFiber_card_pos ha hz β.1
  exact conditional_lower_from_joint _ _ ε (q β.1) _ hc (by positivity) hε (hq β.1).1 (hq β.1).2
    (monomialProfileJoint_local_lower ha hz P ε hε hP α β hab hdiv)

/-- Every source communicates uniformly with every all-free source. -/
theorem monomialProfile_reversible_minorization {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (hs : 0 < s)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ) (q : Fin (2 * s + 1) → ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hq : ∀ j, 0 < q j ∧ q j ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ i j, profileAllowed i j → ε ≤ P i j)
    (α : Σ i, SourceMonomialFiber a z s i) (γ : Degree z s) :
    (z : ℝ) * ε ^ 2 /
        (((a + z + (2 * s + 1) - 1).choose (2 * s + 1) : ℝ) * (2 ^ (2 * s + 1)) ^ 2) ≤
      reversibleWeights
        (fun β : Σ j, TargetMonomialFiber a z s j => q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ))
        (jointConditional (monomialProfileJoint P)
          (fun β => q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ))) α (freeSource hs γ) := by
  have hν (β : Σ j, TargetMonomialFiber a z s j) :
      0 < q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ) := by
    apply div_pos (hq β.1).1
    exact_mod_cast targetMonomialFiber_card_pos ha hz β.1
  have h := reversibleWeights_common_targets (monomialProfileJoint P)
    (fun β => q β.1 / (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ))
    (monomialProfileJoint_nonneg P hP0) hν α (freeSource hs γ) (commonTargetEmbedding α γ)
    (ε / (((a + z + (2 * s + 1) - 1).choose (2 * s + 1) : ℝ) * 2 ^ (2 * s + 1)))
    (ε / 2 ^ (2 * s + 1)) (by positivity) (by positivity)
    (fun t => monomialProfileJoint_uniform_lower ha hz P ε hε hP α (commonTarget α γ t)
      (commonTarget_allowed_left α γ t) (commonTarget_divides_left α γ t))
    (fun t => monomialProfileConditional_uniform_lower ha hz P q hq ε hε hP (freeSource hs γ)
      (commonTarget α γ t) (commonTarget_allowed_free hs α γ t) (commonTarget_divides_free hs α γ t))
  convert h using 1
  simp only [Fintype.card_fin]
  ring

end Froberg
