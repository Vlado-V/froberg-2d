module

public import Froberg.MonomialProfileTransport
public import Froberg.FiniteProfileTransport

@[expose] public section

/-! Exact finite transport on individual monomials with source and target
masses proportional to the actual profile capacities. -/
noncomputable section
namespace Froberg
open Finset Filter MonomialExpansion
open scoped Topology

lemma sourceMonomialFiber_card (a z s : ℕ) (i : Option (Fin s)) :
    Fintype.card (SourceMonomialFiber a z s i) =
      (a + profileSourceIndex i - 1).choose (profileSourceIndex i) *
        (z + (s - profileSourceIndex i) - 1).choose (s - profileSourceIndex i) := by
  let e : SourceMonomialFiber a z s i ≃
      (Degree a (profileSourceIndex i) × Degree z (s - profileSourceIndex i)) := Equiv.refl _
  rw [Fintype.card_congr e, Fintype.card_prod, card_degree, card_degree]

lemma targetMonomialFiber_card (a z s : ℕ) (j : Fin (2 * s + 1)) :
    Fintype.card (TargetMonomialFiber a z s j) =
      (a + j - 1).choose j * (z + (2 * s + 1 - j) - 1).choose (2 * s + 1 - j) := by
  let e : TargetMonomialFiber a z s j ≃
      (Degree a j × Degree z (2 * s + 1 - j)) := Equiv.refl _
  rw [Fintype.card_congr e, Fintype.card_prod, card_degree, card_degree]

lemma sourceMonomialFiber_card_pos {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (i : Option (Fin s)) :
    0 < Fintype.card (SourceMonomialFiber a z s i) := by
  rw [sourceMonomialFiber_card]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

lemma targetMonomialFiber_card_pos {a z s : ℕ} (ha : 0 < a) (hz : 0 < z) (j : Fin (2 * s + 1)) :
    0 < Fintype.card (TargetMonomialFiber a z s j) := by
  rw [targetMonomialFiber_card]
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

lemma finiteSourceProfile_eq_card (H : ℝ) (a z s : ℕ) (i : Option (Fin s)) :
    finiteSourceProfile H s a z i = profileSourceCapacity H i * Fintype.card (SourceMonomialFiber a z s i) := by
  rw [sourceMonomialFiber_card, Nat.cast_mul]
  unfold finiteSourceProfile finiteProfileWeight
  ring

lemma finiteTargetProfile_eq_card (a z s : ℕ) (j : Fin (2 * s + 1)) :
    finiteTargetProfile s a z j = profileTargetCapacity s j * Fintype.card (TargetMonomialFiber a z s j) := by
  rw [targetMonomialFiber_card, Nat.cast_mul]
  unfold finiteTargetProfile finiteProfileWeight
  ring

lemma profileTargetCapacity_pos {s : ℕ} (hs : 0 < s) (j : Fin (2 * s + 1)) :
    0 < profileTargetCapacity s j := by
  have hmono := Nat.choose_le_choose s (show j.val ≤ 2 * s by omega)
  have hpos := Nat.choose_pos (show s - 1 ≤ 2 * s by omega)
  have hpascal := Nat.choose_succ_succ' (2 * s) (s - 1)
  rw [Nat.sub_add_cancel hs] at hpascal
  have hlt : j.val.choose s < (2 * s + 1).choose s := by omega
  unfold profileTargetCapacity
  exact sub_pos.mpr (by exact_mod_cast hlt)

def sourceAtomMass (H : ℝ) (s a z : ℕ) (i : Option (Fin s)) : ℝ :=
  profileSourceCapacity H i / ∑ k, finiteSourceProfile H s a z k

def targetAtomMass (s a z : ℕ) (j : Fin (2 * s + 1)) : ℝ :=
  profileTargetCapacity s j / ∑ k, finiteTargetProfile s a z k

lemma monomialProfileJoint_source_mass {a z s : ℕ} {H : ℝ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ)
    (hP : ∀ i, ∑ j, P i j = finiteSourceProfile H s a z i / ∑ k, finiteSourceProfile H s a z k)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (α : Σ i, SourceMonomialFiber a z s i) :
    ∑ β, monomialProfileJoint P α β = sourceAtomMass H s a z α.1 := by
  rw [monomialProfileJoint_row ha hz P _ hP hPzero, finiteSourceProfile_eq_card]
  have hc : (Fintype.card (SourceMonomialFiber a z s α.1) : ℝ) ≠ 0 := by
    exact_mod_cast (sourceMonomialFiber_card_pos ha hz α.1).ne'
  unfold sourceAtomMass
  field_simp

lemma monomialProfileJoint_target_mass {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ)
    (hP : ∀ j, ∑ i, P i j = finiteTargetProfile s a z j / ∑ k, finiteTargetProfile s a z k)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (β : Σ j, TargetMonomialFiber a z s j) :
    ∑ α, monomialProfileJoint P α β = targetAtomMass s a z β.1 := by
  rw [monomialProfileJoint_column ha hz P _ hP hPzero, finiteTargetProfile_eq_card]
  have hc : (Fintype.card (TargetMonomialFiber a z s β.1) : ℝ) ≠ 0 := by
    exact_mod_cast (targetMonomialFiber_card_pos ha hz β.1).ne'
  unfold targetAtomMass
  field_simp

lemma monomialProfileJoint_zero_of_not_divides {a z s : ℕ} (ha : 0 < a) (hz : 0 < z)
    (P : Option (Fin s) → Fin (2 * s + 1) → ℝ)
    (hPzero : ∀ i j, ¬profileAllowed i j → P i j = 0)
    (α : Σ i, SourceMonomialFiber a z s i) (β : Σ j, TargetMonomialFiber a z s j)
    (hdiv : ¬OuterInjection.joinParts α.2.1.val α.2.2.val ≤
      OuterInjection.joinParts β.2.1.val β.2.2.val) : monomialProfileJoint P α β = 0 := by
  change P α.1 β.1 * localMonomialCoupling α.1 β.1 α.2 β.2 = 0
  by_cases hij : profileAllowed α.1 β.1
  · have hz' : localMonomialCoupling α.1 β.1 α.2 β.2 = 0 := by
      apply le_antisymm _ (localMonomialCoupling_nonneg α.1 β.1 α.2 β.2)
      exact le_of_not_gt (fun hp => hdiv ((localMonomialCoupling_pos_iff ha hz α.1 β.1 hij α.2 β.2).mp hp))
    rw [hz', mul_zero]
  · rw [hPzero α.1 β.1 hij, zero_mul]

/-- The strict limiting transport yields exact atom masses, and a common
positive multiple of the explicit local divisor coupling, for large n. -/
theorem finite_monomial_transport {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
      ∃ J : (Σ i, SourceMonomialFiber (a n) (z n) s i) →
          (Σ j, TargetMonomialFiber (a n) (z n) s j) → ℝ,
        (∀ α, ∑ β, J α β = sourceAtomMass H s (a n) (z n) α.1) ∧
        (∀ β, ∑ α, J α β = targetAtomMass s (a n) (z n) β.1) ∧
        (∀ α β, 0 ≤ J α β) ∧
        (∀ α β, profileAllowed α.1 β.1 →
          ε * localMonomialCoupling α.1 β.1 α.2 β.2 ≤ J α β) ∧
        (∀ α β, ¬profileAllowed α.1 β.1 → J α β = 0) ∧
        (∀ α β, ¬OuterInjection.joinParts α.2.1.val α.2.2.val ≤
          OuterInjection.joinParts β.2.1.val β.2.2.val → J α β = 0) := by
  obtain ⟨ε, hε, hP⟩ := finite_profile_positive_transport hH hσ hσ1 hs a z ha hz har hzr
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hP, ha.eventually (eventually_gt_atTop 0), hz.eventually (eventually_gt_atTop 0)]
    with n hn han hzn
  obtain ⟨P, hPr, hPc, hP0, hPε, hPz⟩ := hn
  refine ⟨monomialProfileJoint P,
    monomialProfileJoint_source_mass han hzn P hPr hPz,
    monomialProfileJoint_target_mass han hzn P hPc hPz,
    monomialProfileJoint_nonneg P hP0, ?_, ?_,
    monomialProfileJoint_zero_of_not_divides han hzn P hPz⟩
  · intro α β hαβ
    exact mul_le_mul_of_nonneg_right (hPε α.1 β.1 hαβ).le
      (localMonomialCoupling_nonneg α.1 β.1 α.2 β.2)
  · intro α β hαβ
    change P α.1 β.1 * _ = 0
    rw [hPz α.1 β.1 hαβ, zero_mul]

end Froberg
