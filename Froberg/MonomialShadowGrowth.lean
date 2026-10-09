module

public import Froberg.ProfileProbabilities
public import Froberg.MonomialMinorization
public import Froberg.MonomialCapacityDecrease
public import Froberg.CapacityTransportGrowth

@[expose] public section

/-! Strict growth for all finite monomial shadows. The transport is the
explicit profile coupling lifted through actual divisor monomials. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

 theorem monomial_shadow_growth {a z s : ℕ}
    (ha : 0 < a) (hz : 0 < z) (hs : 0 < s)
    (P : Option (Fin s) → Fin (2*s+1) → ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (hrow : ∀ i, ∑ j, P i j = finiteSourceProfile (profileAmbientCapacity s) s a z i /
      ∑ k, finiteSourceProfile (profileAmbientCapacity s) s a z k)
    (hcol : ∀ j, ∑ i, P i j = finiteTargetProfile s a z j / ∑ k, finiteTargetProfile s a z k)
    (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hPlower : ∀ i j, profileAllowed i j → ε ≤ P i j)
    (hκupper : κ ≤ monomialMixingCoefficient s a z (profileAmbientCapacity s) ε)
    (ell : (Σ i, SourceMonomialFiber a z s i) → ℝ)
    (b : (Σ j, TargetMonomialFiber a z s j) → ℝ)
    (hell : ∀ α, 0 ≤ ell α ∧ ell α ≤ profileSourceCapacity (profileAmbientCapacity s) α.1)
    (hb : ∀ α β, OuterInjection.joinParts α.2.1.val α.2.2.val ≤
      OuterInjection.joinParts β.2.1.val β.2.2.val →
      min (profileTargetCapacity s β.1) (ell α) ≤ b β) :
    let A := ∑ i, finiteSourceProfile (profileAmbientCapacity s) s a z i
    let T := ∑ j, finiteTargetProfile s a z j
    (T/A) * (∑ α, ell α) + (min (ε/profileAmbientCapacity s) (κ/2) / 4) *
      (T/A) * min (∑ α, ell α) (A-∑ α, ell α) ≤ ∑ β, b β := by
  dsimp only
  let H := profileAmbientCapacity s
  let A := ∑ i, finiteSourceProfile H s a z i
  let T := ∑ j, finiteTargetProfile s a z j
  let p := fun i => finiteSourceProfile H s a z i / A
  let q := fun j => finiteTargetProfile s a z j / T
  let ν := fun β : Σ j, TargetMonomialFiber a z s j => q β.1 /
    (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ)
  let μ := embeddedUniform (freeSourceEmbedding (a := a) (z := z) hs)
  letI := degree_nonempty hz s
  have hH : 1 < H := profileAmbientCapacity_gt_one hs
  have hA : 0 < A := finiteSourceProfile_total_pos hH ha hz
  have hT : 0 < T := finiteTargetProfile_total_pos ha hz hs
  have hp (i : Option (Fin s)) : 0 < p i ∧ p i ≤ 1 :=
    normalized_weight_bounds _ (finiteSourceProfile_pos hH ha hz) i
  have hq (j : Fin (2*s+1)) : 0 < q j ∧ q j ≤ 1 :=
    normalized_weight_bounds _ (finiteTargetProfile_pos ha hz hs) j
  have hν : ν = fun β : Σ j, TargetMonomialFiber a z s j => profileTargetCapacity s β.1 / T := by
    funext β
    exact normalized_target_atom ha hz β.1
  have hminor := monomial_minorization ha hz hs (lt_trans (by norm_num) hH) hA P q hP0 hq ε hε hPlower
  change ∀ α γ, monomialMixingCoefficient s a z H ε * sourceAtomMass H s a z α.1 * μ γ ≤
    reversibleWeights ν (jointConditional (monomialProfileJoint P) ν) α γ at hminor
  rw [hν] at hminor
  apply capacity_transport_growth
    (fun α => profileSourceCapacity H α.1) ell (fun β => profileTargetCapacity s β.1) b
    (monomialProfileJoint P) μ A T (ε/H) κ hA hT
    (fun α => profileSourceCapacity_pos hH α.1) (fun β => profileTargetCapacity_pos hs β.1)
    (sourceProfile_sum_atoms H a z s) (targetProfile_sum_atoms a z s) hell
    (monomialProfileJoint_nonneg P hP0)
    (monomialProfileJoint_source_mass ha hz P hrow hPzero)
    (monomialProfileJoint_target_mass ha hz P hcol hPzero)
    (embeddedUniform_sum _) (embeddedUniform_nonneg _)
    (div_nonneg hε (profileAmbientCapacity_pos s).le) hκ
  · intro α β hpos
    exact profileTargetCapacity_le_source α.1 β.1 (monomialProfileJoint_pos_allowed P hPzero α β hpos)
  · intro α β hpos
    apply hb α β
    by_contra hnot
    have he := monomialProfileJoint_zero_of_not_divides ha hz P hPzero α β hnot
    linarith
  · intro α γ
    apply le_trans _ (hminor α γ)
    apply mul_le_mul_of_nonneg_right _ (embeddedUniform_nonneg _ γ)
    exact mul_le_mul_of_nonneg_right hκupper (div_nonneg (profileSourceCapacity_pos hH α.1).le hA.le)
  · intro α
    have hh := monomial_capacity_decrease ha hz hs P p hP0 hPzero
      (fun i => (hp i).2) ε hε hPlower α
    change (ε/H) * (p α.1 / (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ)) ≤ _ at hh
    have hpα : p α.1 / (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ) =
        profileSourceCapacity H α.1 / A := normalized_source_atom ha hz α.1
    rw [hpα] at hh
    exact hh

end Froberg
