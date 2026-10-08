import Froberg.ScaledMonomialShadow
import Froberg.ProfileCapacityTotals
import Froberg.SourceFibers

/-! Transport growth expressed directly on polynomial exponents, with
all target exponents included. -/
noncomputable section
namespace Froberg
open Finset Filter MonomialExpansion OuterInjection
open scoped Topology

def degreeExponentEquiv (n d : ℕ) : Degree n d ≃ Quartic.HomogeneousCoefficientCoordinates.Exponent n d where
  toFun a := ⟨a.val, degree_val a⟩
  invFun a := ⟨a.val, mem_exponents.mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma positive_target_sum_le {a z s : ℕ} (b : Degree (a+z) (2*s+1) → ℝ) (hb : ∀ β, 0 ≤ b β) :
    (∑ β : Σ j, TargetMonomialFiber a z s j, b (targetExponent β).val) ≤ ∑ β, b β := by
  classical
  have he := (targetMonomialEquiv a z s).sum_comp (fun β => b β.val)
  change (∑ β : Σ j, TargetMonomialFiber a z s j, b (targetExponent β).val) =
    ∑ β : PositiveTargetMonomial a z s, b β.val at he
  rw [he]
  have hh := Fintype.sum_subtype_add_sum_subtype
    (fun β : Degree (a+z) (2*s+1) => (corePart β.val).degree < 2*s+1) b
  have hn : 0 ≤ ∑ β : {β : Degree (a+z) (2*s+1) // ¬(corePart β.val).degree < 2*s+1}, b β.val :=
    sum_nonneg fun β _ => hb β.val
  change (∑ β : PositiveTargetMonomial a z s, b β.val) + _ = _ at hh
  linarith

theorem uniform_exponent_shadow {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ) / n) atTop (𝓝 (1-σ)))
    (haz : ∀ n, a n+z n=n) (K : ℝ) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      ∀ (ell : Degree (a n+z n) s → ℝ) (b : Degree (a n+z n) (2*s+1) → ℝ),
      (∀ α, 0 ≤ ell α ∧ ell α ≤ K*(profileAmbientCapacity s -
        if (corePart α.val).degree = s then 1 else 0)) →
      (∀ β, 0 ≤ b β) →
      (∀ α β, α.val ≤ β.val →
        min (K*(profileAmbientCapacity s - ((corePart β.val).degree.choose s : ℝ))) (ell α) ≤ b β) →
      let A := ∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i
      let T := ∑ j, finiteTargetProfile s (a n) (z n) j
      (T/A)*(∑ α, ell α)+c*(T/A)*min (∑ α, ell α) (K*A-∑ α, ell α) ≤ ∑ β, b β := by
  obtain ⟨c,hc,hev⟩ := uniform_scaled_monomial_shadow hσ hσ1 hs a z ha hz har hzr haz K hK
  refine ⟨c,hc,hev.mono ?_⟩
  intro n hn ell b hell hb hshadow
  have hl (α : Σ i, SourceMonomialFiber (a n) (z n) s i) :
      0 ≤ ell (sourceExponent α) ∧ ell (sourceExponent α) ≤
        K*profileSourceCapacity (profileAmbientCapacity s) α.1 := by
    simpa only [source_capacity_at_exponent] using hell (sourceExponent α)
  have hs' (α : Σ i, SourceMonomialFiber (a n) (z n) s i)
      (β : Σ j, TargetMonomialFiber (a n) (z n) s j)
      (hdiv : joinParts α.2.1.val α.2.2.val ≤ joinParts β.2.1.val β.2.2.val) :
      min (K*profileTargetCapacity s β.1) (ell (sourceExponent α)) ≤ b (targetExponent β).val := by
    simpa only [target_capacity_at_exponent] using hshadow (sourceExponent α) (targetExponent β).val hdiv
  have hh := hn (fun α => ell (sourceExponent α)) (fun β => b (targetExponent β).val) hl hs'
  have he := (sourceMonomialEquiv (a n) (z n) s).sum_comp ell
  change (∑ α : Σ i, SourceMonomialFiber (a n) (z n) s i, ell (sourceExponent α)) = ∑ α, ell α at he
  dsimp only at hh ⊢
  rw [he] at hh
  exact hh.trans (positive_target_sum_le b hb)

end Froberg
