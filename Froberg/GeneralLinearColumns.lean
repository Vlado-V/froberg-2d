import Froberg.DetectedPrivateOutputs
import Froberg.UniversalMixedPosition

/-! A finite family of pairwise independent linear forms, and its common
quadratic detector, constructed over every infinite field. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K : Type*} [Field K] [Infinite K] {h b c : ℕ}

/-- Arbitrarily many private linear columns may be put in pairwise general position. -/
theorem exists_pairwise_independent_linear_columns (hh : 2≤h) (b : ℕ) :
    ∃ w : Fin b → Forms K h 1,
      (∀ i, w i ≠ 0) ∧ (∀ p : GeneratorPair b,
        LinearIndependent K (![w p.val.1,w p.val.2] : Fin 2 → Forms K h 1)) := by
  classical
  have hhpos : 0<h := by omega
  let e : (Fin h → K) ≃ₗ[K] Forms K h 1 := LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_forms K h 1 hhpos]
    simp)
  obtain ⟨v,hv,_⟩ := MixedExterior.exists_universal_mixed_vectors (K := K) (α := Fin b) h
  let w : Fin b → Forms K h 1 := fun i => e (v i)
  have hfull (S : Finset (Fin b)) (hS : S.card≤h) :
      LinearIndependent K (fun i : S => w i.val) :=
    (hv S hS).map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  refine ⟨w,?_,?_⟩
  · intro i
    exact (hfull {i} (by simp; omega)).ne_zero ⟨i,by simp⟩
  · intro p
    let S : Finset (Fin b) := {p.val.1,p.val.2}
    have hS : S.card≤h := by
      have hcard : S.card=2 := by simp [S,ne_of_lt p.property]
      omega
    let f : Fin 2 → S := ![⟨p.val.1,by simp [S]⟩,⟨p.val.2,by simp [S]⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · have hh := congrArg Subtype.val hij
        exact False.elim ((ne_of_lt p.property) hh)
      · have hh := congrArg Subtype.val hij
        exact False.elim ((ne_of_lt p.property) hh.symm)
      · rfl
    have hi := (hfull S hS).comp f hf
    convert hi using 1
    ext i
    fin_cases i <;> rfl

/-- The private detector exists with exactly the manuscript's 2h−1 target
bound; its columns and pair relations are the actual quadratic products. -/
theorem exists_general_detected_private_outputs (hh : 2≤h) (hc : 2*h-1≤c) (b : ℕ) :
    ∃ (w : Fin b → Forms K h 1) (L : Forms K h 2 →ₗ[K] (Fin c → K)),
      (∀ i, w i ≠ 0) ∧
      (∀ i, Function.Injective (L.comp (mulForm (w i)))) ∧
      (∀ p : GeneratorPair b, ∀ x y,
        L (mulForm (w p.val.1) x)+L (mulForm (w p.val.2) y)=0 →
        ∃ t : K, x=t • w p.val.2 ∧ y=(-t) • w p.val.1) := by
  obtain ⟨w,hw,hpair⟩ := exists_pairwise_independent_linear_columns (K := K) hh b
  obtain ⟨L,hL,hrel⟩ := exists_detected_private_outputs (by omega) hc w hw hpair
  exact ⟨w,L,hw,hL,hrel⟩

end Froberg
