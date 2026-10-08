import Froberg.DetectedLinearPairs

/-! Actual quadratic output projections for finitely many private linear
columns. The only target dimension cost is 2h−1. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K : Type*} [Field K] [Infinite K] {h b c : ℕ}

/-- A single quadratic detector retains each private column injectively and
retains precisely the one-dimensional classical overlap of every pair. -/
theorem exists_detected_private_outputs (hh : 0<h) (hc : 2*h-1≤c)
    (w : Fin b → Forms K h 1) (hw : ∀ i, w i ≠ 0)
    (hpair : ∀ p : GeneratorPair b,
      LinearIndependent K (![w p.val.1,w p.val.2] : Fin 2 → Forms K h 1)) :
    ∃ L : Forms K h 2 →ₗ[K] (Fin c → K),
      (∀ i, Function.Injective (L.comp (mulForm (w i)))) ∧
      (∀ p : GeneratorPair b, ∀ x y,
        L (mulForm (w p.val.1) x)+L (mulForm (w p.val.2) y)=0 →
        ∃ t : K, x=t • w p.val.2 ∧ y=(-t) • w p.val.1) := by
  classical
  let pair (p : GeneratorPair b) : Fin 2 → Forms K h 1 := ![w p.val.1,w p.val.2]
  let U : Fin b ⊕ GeneratorPair b → Submodule K (Forms K h 2) :=
    Sum.elim (fun i => (mulForm (w i)).range) (fun p => (endpointMultiplication (pair p)).range)
  have hdim : ∀ i, finrank K (U i)≤finrank K (Fin c → K) := by
    intro i
    simp only [Module.finrank_pi_fintype,finrank_self,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one]
    rcases i with i | p
    · change finrank K (mulForm (w i)).range≤c
      have hwi : (w i).val ≠ 0 := fun hz => hw i (Subtype.ext hz)
      rw [LinearMap.finrank_range_of_inj (mulForm_injective (w i) hwi),finrank_forms K h 1 hh]
      simp only [Nat.add_sub_cancel,Nat.choose_one_right]
      omega
    · change finrank K (endpointMultiplication (pair p)).range≤c
      rw [linear_pair_output_finrank hh (pair p) (hpair p)]
      exact hc
  obtain ⟨L,hL⟩ := exists_finite_subspace_projection U hdim
  refine ⟨L,?_,?_⟩
  · intro i x y hxy
    have hz : (⟨mulForm (w i) x,LinearMap.mem_range_self _ x⟩ : (mulForm (w i)).range) =
        ⟨mulForm (w i) y,LinearMap.mem_range_self _ y⟩ :=
      hL (Sum.inl i) hxy
    exact mulForm_injective (w i) (fun hz => hw i (Subtype.ext hz)) (congrArg Subtype.val hz)
  · intro p x y hxy
    exact detected_linear_pair_relation hh (pair p) (hpair p) L (hL (Sum.inr p)) x y hxy

end Froberg
