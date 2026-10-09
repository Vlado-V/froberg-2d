module

public import Froberg.BinomialProfiles

@[expose] public section

/-! Explicit strictly positive transport for every allowed outer-module
profile pair. The construction diverts a marked Bernoulli event to the last
source row and preserves every target marginal exactly. -/
noncomputable section
namespace Froberg
open Finset

def profileSourceIndex {s : ℕ} : Option (Fin s) → ℕ
  | some i => i
  | none => s

def profileAllowed {s : ℕ} (i : Option (Fin s)) (j : Fin (2 * s + 1)) : Prop :=
  profileSourceIndex i ≤ j ∧ (j : ℕ) ≤ profileSourceIndex i + s + 1

def profileDiversionRate (H σ : ℝ) (s : ℕ) : ℝ := (H - 1) / (H - σ ^ s)

def profileSourceMass (H σ : ℝ) (s : ℕ) : Option (Fin s) → ℝ
  | some i => H * profileBinomial σ s i / (H - σ ^ s)
  | none => (H - 1) * σ ^ s / (H - σ ^ s)

def profileTargetMass (σ : ℝ) (s : ℕ) (j : Fin (2 * s + 1)) : ℝ :=
  ∑ i, profileJoint σ s i j

def explicitProfileTransport (H σ : ℝ) (s : ℕ) : Option (Fin s) → Fin (2 * s + 1) → ℝ :=
  divertedTransport (profileJoint σ s) (profileMarkedJoint σ s) (profileDiversionRate H σ s)

theorem profileDiversionRate_bounds {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    0 < profileDiversionRate H σ s ∧ profileDiversionRate H σ s < 1 := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  have hden : 0 < H - σ ^ s := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · exact (div_lt_one hden).mpr (by linarith)

theorem explicitProfileTransport_row {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) (i : Option (Fin s)) :
    ∑ j, explicitProfileTransport H σ s i j = profileSourceMass H σ s i := by
  have hp : σ ^ s < 1 := pow_lt_one₀ hσ.le hσ1 (by omega)
  have hn : H - σ ^ s ≠ 0 := by linarith
  have hp' : 1 - σ ^ s ≠ 0 := by linarith
  cases i with
  | none =>
      rw [explicitProfileTransport, divertedTransport_new_row _ _ _ _ _
        (profileConditional_sum hσ hσ1 hs) (profileMarkedJoint_row σ s)]
      simp only [profileDiversionRate, profileSourceMass]
      ring
  | some i =>
      rw [explicitProfileTransport, divertedTransport_old_row _ _ _ _ _
        (profileJoint_row σ s) (profileMarkedJoint_row σ s)]
      simp only [profileDiversionRate, profileSourceMass, profileConditional]
      field_simp
      ring

theorem explicitProfileTransport_column (H σ : ℝ) (s : ℕ) (j : Fin (2 * s + 1)) :
    ∑ i, explicitProfileTransport H σ s i j = profileTargetMass σ s j :=
  divertedTransport_column _ _ _ _

theorem profileTargetMass_sum {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    ∑ j, profileTargetMass σ s j = 1 := by
  simp only [profileTargetMass]
  rw [sum_comm]
  simp only [profileJoint_row]
  exact profileConditional_sum hσ hσ1 hs

theorem profileSourceMass_sum {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    ∑ i, profileSourceMass H σ s i = 1 := by
  simp_rw [← explicitProfileTransport_row hH hσ hσ1 hs]
  rw [sum_comm]
  simp only [explicitProfileTransport_column]
  exact profileTargetMass_sum hσ hσ1 hs

theorem explicitProfileTransport_nonneg {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s) :
    ∀ i j, 0 ≤ explicitProfileTransport H σ s i j := by
  have ht := profileDiversionRate_bounds hH hσ hσ1 hs
  exact divertedTransport_nonneg _ _ _ ht.1.le ht.2.le
    (profileMarkedJoint_nonneg hσ hσ1 hs) (profileMarkedJoint_le hσ hσ1 hs)

theorem explicitProfileTransport_pos {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : profileAllowed i j) :
    0 < explicitProfileTransport H σ s i j := by
  have ht := profileDiversionRate_bounds hH hσ hσ1 hs
  cases i with
  | none =>
      exact divertedTransport_new_pos _ _ _ ht.1 (profileMarkedJoint_nonneg hσ hσ1 hs) j
        (profileMarkedJoint_positive_column hσ hσ1 hs j hij.1)
  | some i =>
      exact divertedTransport_old_pos _ _ _ ht.1.le ht.2 i j
        (profileJoint_pos hσ hσ1 hs i j hij.1 hij.2)
        (profileMarkedJoint_nonneg hσ hσ1 hs i j) (profileMarkedJoint_le hσ hσ1 hs i j)

theorem explicitProfileTransport_zero {H σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (i : Option (Fin s)) (j : Fin (2 * s + 1)) (hij : ¬profileAllowed i j) :
    explicitProfileTransport H σ s i j = 0 := by
  cases i with
  | none =>
      have hj : (j : ℕ) < s := by
        simp only [profileAllowed, profileSourceIndex] at hij
        omega
      simp only [explicitProfileTransport, divertedTransport,
        profileMarkedJoint_zero_column _ _ hj, sum_const_zero, mul_zero]
  | some i =>
      have hp := profileJoint_zero (σ := σ) i j hij
      have hd : profileMarkedJoint σ s i j = 0 := by
        have h₁ := profileMarkedJoint_nonneg hσ hσ1 hs i j
        have h₂ := profileMarkedJoint_le hσ hσ1 hs i j
        linarith
      exact divertedTransport_zero _ _ _ i j hp hd

def profileHub (s : ℕ) : Fin (2 * s + 1) := ⟨s, by omega⟩

def profileParent {s : ℕ} (hs : 0 < s) (j : Fin (2 * s + 1)) : Option (Fin s) :=
  if (j : ℕ) ≤ s + 1 then some ⟨0, hs⟩ else some ⟨j - (s + 1), by omega⟩

theorem profileHub_allowed (s : ℕ) (i : Option (Fin s)) : profileAllowed i (profileHub s) := by
  cases i <;> simp only [profileAllowed, profileSourceIndex, profileHub] <;> constructor <;> omega

theorem profileParent_allowed {s : ℕ} (hs : 0 < s) (j : Fin (2 * s + 1)) :
    profileAllowed (profileParent hs j) j := by
  unfold profileParent
  split_ifs <;> simp only [profileAllowed, profileSourceIndex] <;> constructor <;> omega

end Froberg
