import Quartic.Koszul
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The linear algebra in the symmetric evaluation estimate

The generic points are represented by a proper filter which eventually avoids
every nonzero linear functional. This is the exact nondegeneracy property used
in the manuscript's induction. No claim about an algebraic variety producing
such a filter is assumed or proved here.
-/

noncomputable section

universe u v w

namespace Quartic.SymmetricEvaluation

open Module Filter

variable {K : Type v} [Field K]
  {V : Type w} [AddCommGroup V] [Module K V]

def evaluation {U : Type u} [AddCommGroup U] [Module K U]
    (H : U →ₗ[K] (V →ₗ[K] V →ₗ[K] K)) (x : V) : U →ₗ[K] (V →ₗ[K] K) :=
  (LinearMap.applyₗ (R := K) x).comp H

@[simp] theorem evaluation_apply {U : Type u} [AddCommGroup U] [Module K U]
    (H : U →ₗ[K] (V →ₗ[K] V →ₗ[K] K)) (x : V) (u : U) :
    evaluation H x u = H u x := rfl

/-- Persistent avoidance of each hyperplane through the origin. -/
def AvoidsHyperplanes (F : Filter V) : Prop :=
  ∀ L : V →ₗ[K] K, L ≠ 0 → ∀ᶠ x in F, L x ≠ 0

/-- A symmetric family whose generic evaluation rank is at most `b` has
dimension at most `choose (b+1) 2`. The genericity hypothesis is stated explicitly
as a proper filter avoiding every nonzero linear functional. -/
theorem dimension_bound (F : Filter V) [F.NeBot] (hF : AvoidsHyperplanes (K := K) F)
    (b : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (H : U →ₗ[K] (V →ₗ[K] V →ₗ[K] K)), Function.Injective H →
      (∀ u x y, H u x y = H u y x) →
      (∀ᶠ x in F, finrank K (LinearMap.range (evaluation H x)) ≤ b) →
      finrank K U ≤ (b + 1).choose 2 := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro U _ _ _ H hH hsym hrank
    by_cases hzero : finrank K U = 0
    · simp [hzero]
    obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hzero)
    have hex : ∃ x y, H u x y ≠ 0 := by
      by_contra h
      push Not at h
      apply hu
      apply hH
      ext x y
      simpa using h x y
    obtain ⟨x, y, hxy⟩ := hex
    have hfunctional : H u x ≠ 0 := by
      intro h
      exact hxy (by rw [h]; rfl)
    obtain ⟨v₀, hv₀, hv⟩ := (hrank.and (hF _ hfunctional)).exists
    have hvx : H u v₀ x ≠ 0 := by rwa [hsym] 
    have hvnonzero : H u v₀ ≠ 0 := by
      intro h
      exact hvx (by rw [h]; rfl)
    let E := evaluation H v₀
    have hpos : 0 < finrank K (LinearMap.range E) := by
      apply Nat.pos_of_ne_zero
      intro h
      have hz : LinearMap.range E = ⊥ := Submodule.finrank_eq_zero.mp h
      have hmem : E u ∈ LinearMap.range E := ⟨u, rfl⟩
      rw [hz] at hmem
      exact hvnonzero hmem
    have hb : 0 < b := lt_of_lt_of_le hpos hv₀
    let U₀ := E.ker
    let H₀ : U₀ →ₗ[K] (V →ₗ[K] V →ₗ[K] K) := H.comp U₀.subtype
    have hH₀ : Function.Injective H₀ := hH.comp (Submodule.injective_subtype _)
    have hsym₀ : ∀ z x y, H₀ z x y = H₀ z y x := fun z x y => hsym z.val x y
    have hrank₀ : ∀ᶠ w in F,
        finrank K (LinearMap.range (evaluation H₀ w)) ≤ b - 1 := by
      filter_upwards [hrank, hF _ hvnonzero] with w hw hwv
      have hle : LinearMap.range (evaluation H₀ w) ≤ LinearMap.range (evaluation H w) := by
        rintro _ ⟨z, rfl⟩
        exact ⟨z.val, rfl⟩
      have hnot : evaluation H w u ∉ LinearMap.range (evaluation H₀ w) := by
        rintro ⟨z, hz⟩
        have hzv : H z.val v₀ w = 0 := LinearMap.congr_fun z.property w
        have heq : H z.val w v₀ = H u w v₀ := LinearMap.congr_fun hz v₀
        apply hwv
        calc
          H u v₀ w = H u w v₀ := hsym u v₀ w
          _ = H z.val w v₀ := heq.symm
          _ = H z.val v₀ w := hsym z.val w v₀
          _ = 0 := hzv
      have hlt : LinearMap.range (evaluation H₀ w) < LinearMap.range (evaluation H w) :=
        lt_of_le_of_ne hle (fun heq => hnot (heq ▸ (show evaluation H w u ∈
          LinearMap.range (evaluation H w) from ⟨u, rfl⟩)))
      have hdim := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hdim₀ := ih (b - 1) (by omega) H₀ hH₀ hsym₀ hrank₀
    have hnull := E.finrank_range_add_finrank_ker
    have hpred : b - 1 + 1 = b := by omega
    rw [hpred] at hdim₀
    have hchoose : (b + 1).choose 2 = b.choose 2 + b := by
      rw [Nat.choose_succ_succ]
      simp [Nat.choose_one_right, add_comm]
    rw [hchoose]
    change finrank K E.ker ≤ b.choose 2 at hdim₀
    change finrank K E.range ≤ b at hv₀
    omega

end Quartic.SymmetricEvaluation
