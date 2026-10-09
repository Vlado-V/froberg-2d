module

public import Mathlib

@[expose] public section

/-! Stability of a strictly positive finite transport. The allowed graph
has a column adjacent to every row; every other column has a chosen parent.
The correction below realizes perturbed marginals exactly. -/
noncomputable section
namespace Froberg
open Finset Filter
open scoped Topology
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def transportCorrection (P : I → J → ℝ) (hub : J) (parent : J → I)
    (a : I → ℝ) (b : J → ℝ) (i : I) (j : J) : ℝ :=
  P i j + (if parent j = i then b j - ∑ k, P k j else 0) +
    if j = hub then a i - ∑ k, P i k -
      ∑ k, (if parent k = i then b k - ∑ l, P l k else 0) else 0

theorem transportCorrection_row (P : I → J → ℝ) (hub : J) (parent : J → I)
    (a : I → ℝ) (b : J → ℝ) (i : I) :
    ∑ j, transportCorrection P hub parent a b i j = a i := by
  simp only [transportCorrection, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  ring

theorem transportCorrection_column (P : I → J → ℝ) (hub : J) (parent : J → I)
    (a : I → ℝ) (b : J → ℝ) (hab : ∑ i, a i = ∑ j, b j) (j : J) :
    ∑ i, transportCorrection P hub parent a b i j = b j := by
  by_cases hj : j = hub
  · subst j
    simp only [transportCorrection, if_true, sum_add_distrib, sum_sub_distrib]
    have howned : ∑ i, (if parent hub = i then b hub - ∑ k, P k hub else 0) =
        b hub - ∑ k, P k hub := by simp
    have htotal : ∑ i, ∑ k, (if parent k = i then b k - ∑ l, P l k else 0) =
        ∑ k, b k - ∑ k, ∑ l, P l k := by
      rw [sum_comm]
      simp [sum_sub_distrib]
    rw [howned, htotal, hab, sum_comm (f := P)]
    ring
  · simp only [transportCorrection, hj, if_false, add_zero, sum_add_distrib]
    simp

theorem transportCorrection_zero (P : I → J → ℝ) (hub : J) (parent : J → I)
    (a : I → ℝ) (b : J → ℝ) (R : I → J → Prop)
    (hP : ∀ i j, ¬R i j → P i j = 0)
    (hhub : ∀ i, R i hub) (hparent : ∀ j, R (parent j) j)
    (i : I) (j : J) (hij : ¬R i j) : transportCorrection P hub parent a b i j = 0 := by
  have hj : j ≠ hub := by rintro rfl; exact hij (hhub i)
  have hp : parent j ≠ i := by rintro rfl; exact hij (hparent j)
  simp only [transportCorrection, hP i j hij, hp, hj, if_false, add_zero]

theorem transportCorrection_limit (P : I → J → ℝ) (hub : J) (parent : J → I)
    (a : ℕ → I → ℝ) (b : ℕ → J → ℝ)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (∑ j, P i j)))
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (∑ i, P i j))) (i : I) (j : J) :
    Tendsto (fun n => transportCorrection P hub parent (a n) (b n) i j) atTop (𝓝 (P i j)) := by
  have hd (j : J) : Tendsto (fun n => b n j - ∑ k, P k j) atTop (𝓝 0) := by
    simpa only [sub_self] using (hb j).sub_const (∑ k, P k j)
  have he (j : J) : Tendsto (fun n => if parent j = i then b n j - ∑ k, P k j else 0)
      atTop (𝓝 0) := by
    split_ifs <;> first | exact hd j | exact tendsto_const_nhds
  have hsum := tendsto_finsetSum univ (fun k _ => he k)
  simp only [sum_const_zero] at hsum
  have hr : Tendsto (fun n => a n i - ∑ k, P i k -
      ∑ k, (if parent k = i then b n k - ∑ l, P l k else 0)) atTop (𝓝 0) := by
    simpa only [sub_self, sub_zero] using ((ha i).sub_const (∑ k, P i k)).sub hsum
  unfold transportCorrection
  by_cases hj : j = hub
  · subst j
    simp only [if_true]
    simpa only [add_zero] using ((he hub).const_add (P i hub)).add hr
  · simp only [hj, if_false, add_zero]
    simpa only [add_zero] using (he j).const_add (P i j)

theorem stable_positive_transport (P : I → J → ℝ) (hub : J) (parent : J → I)
    (R : I → J → Prop) (hpos : ∀ i j, R i j → 0 < P i j)
    (hzero : ∀ i j, ¬R i j → P i j = 0)
    (hhub : ∀ i, R i hub) (hparent : ∀ j, R (parent j) j)
    (a : ℕ → I → ℝ) (b : ℕ → J → ℝ)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (∑ j, P i j)))
    (hb : ∀ j, Tendsto (fun n => b n j) atTop (𝓝 (∑ i, P i j)))
    (hab : ∀ᶠ n : ℕ in atTop, ∑ i, a n i = ∑ j, b n j) :
    ∀ᶠ n : ℕ in atTop, ∃ T : I → J → ℝ,
      (∀ i, ∑ j, T i j = a n i) ∧ (∀ j, ∑ i, T i j = b n j) ∧
      (∀ i j, 0 ≤ T i j) ∧ (∀ i j, R i j → P i j / 2 < T i j) ∧
      (∀ i j, ¬R i j → T i j = 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ i j, R i j →
      P i j / 2 < transportCorrection P hub parent (a n) (b n) i j := by
    apply (eventually_all).mpr
    intro i
    apply (eventually_all).mpr
    intro j
    by_cases hij : R i j
    · have hhalf : P i j / 2 < P i j := by linarith [hpos i j hij]
      exact ((transportCorrection_limit P hub parent a b ha hb i j).eventually
        (lt_mem_nhds hhalf)).mono fun _ hn _ => hn
    · exact Eventually.of_forall fun _ hh => False.elim (hij hh)
  filter_upwards [hbound, hab] with n hn habn
  refine ⟨transportCorrection P hub parent (a n) (b n),
    transportCorrection_row P hub parent (a n) (b n),
    transportCorrection_column P hub parent (a n) (b n) habn, ?_, hn, ?_⟩
  · intro i j
    by_cases hij : R i j
    · have := hn i j hij
      linarith [hpos i j hij]
    · rw [transportCorrection_zero P hub parent (a n) (b n) R hzero hhub hparent i j hij]
  · exact transportCorrection_zero P hub parent (a n) (b n) R hzero hhub hparent

end Froberg
