import Froberg.TransportVariance

/-! Conditional kernels of finite joint distributions and a direct
minorization from a family of distinct common target monomials. -/
noncomputable section
namespace Froberg
open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

def jointConditional (P : I → J → ℝ) (ν : J → ℝ) (j : J) (i : I) : ℝ := P i j / ν j

lemma jointConditional_nonneg (P : I → J → ℝ) (ν : J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hν : ∀ j, 0 ≤ ν j) (j : J) (i : I) :
    0 ≤ jointConditional P ν j i := div_nonneg (hP i j) (hν j)

lemma jointConditional_row (P : I → J → ℝ) (ν : J → ℝ)
    (hcolumn : ∀ j, ∑ i, P i j = ν j) (hν : ∀ j, ν j ≠ 0) (j : J) :
    ∑ i, jointConditional P ν j i = 1 := by
  simp only [jointConditional, ← sum_div, hcolumn, div_self (hν j)]

lemma jointConditional_joint (P : I → J → ℝ) (ν : J → ℝ)
    (hν : ∀ j, ν j ≠ 0) (i : I) (j : J) :
    ν j * jointConditional P ν j i = P i j := by
  unfold jointConditional
  field_simp [hν j]

lemma jointConditional_source (P : I → J → ℝ) (ν : J → ℝ) (p : I → ℝ)
    (hrow : ∀ i, ∑ j, P i j = p i) (hν : ∀ j, ν j ≠ 0) (i : I) :
    ∑ j, ν j * jointConditional P ν j i = p i := by
  simp only [jointConditional_joint P ν hν, hrow]

/-- Any injective collection of common targets supplies a quantitative
lower bound on the source-to-source reversible kernel. -/
theorem reversibleWeights_common_targets {A : Type*} [Fintype A]
    (P : I → J → ℝ) (ν : J → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hν : ∀ j, 0 < ν j) (i k : I) (targets : A ↪ J) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hfirst : ∀ a, u ≤ P i (targets a))
    (hsecond : ∀ a, v ≤ jointConditional P ν (targets a) k) :
    (Fintype.card A : ℝ) * u * v ≤ reversibleWeights ν (jointConditional P ν) i k := by
  classical
  have hν' : ∀ j, ν j ≠ 0 := fun j => (hν j).ne'
  have hnonneg (j : J) : 0 ≤ P i j * jointConditional P ν j k :=
    mul_nonneg (hP i j) (jointConditional_nonneg P ν hP (fun j => (hν j).le) j k)
  unfold reversibleWeights
  simp only [jointConditional_joint P ν hν']
  calc
    _ = ∑ a : A, u * v := by simp [mul_assoc]
    _ ≤ ∑ a : A, P i (targets a) * jointConditional P ν (targets a) k := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul (hfirst a) (hsecond a) hv (hP i (targets a))
    _ = ∑ j ∈ univ.image targets, P i j * jointConditional P ν j k := by
      rw [sum_image]
      exact fun a _ b _ h => targets.injective h
    _ ≤ ∑ j : J, P i j * jointConditional P ν j k :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hnonneg j)

end Froberg
