module

public import Froberg.ProfileWeights
public import Froberg.TransportStability

@[expose] public section

/-! The limiting transport persists for the exact finite-dimensional
source and coarse target profiles, with one positive bound on every
allowed edge. -/
noncomputable section
namespace Froberg
open Finset Filter
open scoped Topology

def finiteSourceProfile (H : ℝ) (s a b : ℕ) (i : Option (Fin s)) : ℝ :=
  finiteProfileWeight (profileSourceCapacity H i) s (profileSourceIndex i) a b

def finiteTargetProfile (s a b : ℕ) (j : Fin (2 * s + 1)) : ℝ :=
  finiteProfileWeight (profileTargetCapacity s j) (2 * s + 1) j a b

theorem sourceProfile_normalized_limit {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    (∀ i, Tendsto (fun n => finiteSourceProfile H s (a n) (b n) i /
      ∑ k, finiteSourceProfile H s (a n) (b n) k) atTop (𝓝 (profileSourceMass H σ s i))) ∧
    (∀ᶠ n : ℕ in atTop, 0 < ∑ k, finiteSourceProfile H s (a n) (b n) k) := by
  apply normalized_scaled_weights_limit _ _ s (sourceProfileScale H σ s)
    (sourceProfileScale_pos hH hσ hσ1 hs) (profileSourceMass_sum hH hσ hσ1 hs)
  intro i
  have hi : profileSourceIndex i ≤ s := by cases i <;> simp only [profileSourceIndex] <;> omega
  have hh := finiteProfileWeight_limit a b σ (profileSourceCapacity H i) s
    (profileSourceIndex i) hi ha hb har hbr
  rwa [raw_sourceProfileWeight hH hσ hσ1 hs i] at hh

theorem targetProfile_normalized_limit {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    (∀ j, Tendsto (fun n => finiteTargetProfile s (a n) (b n) j /
      ∑ k, finiteTargetProfile s (a n) (b n) k) atTop (𝓝 (profileTargetMass σ s j))) ∧
    (∀ᶠ n : ℕ in atTop, 0 < ∑ k, finiteTargetProfile s (a n) (b n) k) := by
  apply normalized_scaled_weights_limit _ _ (2 * s + 1) (targetProfileScale σ s)
    (targetProfileScale_pos hσ hσ1 hs) (profileTargetMass_sum hσ hσ1 hs)
  intro j
  have hh := finiteProfileWeight_limit a b σ (profileTargetCapacity s j) (2 * s + 1) j
    (by omega) ha hb har hbr
  rwa [raw_targetProfileWeight hσ hσ1 hs j] at hh

private theorem finite_positive_lower_bound {I : Type*} (S : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
      obtain ⟨ε, hε, hb⟩ := ih (fun j hj => hf j (mem_insert_of_mem hj))
      refine ⟨min (f i) ε, lt_min (hf i (mem_insert_self _ _)) hε, ?_⟩
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb j hj)

theorem finite_profile_positive_transport {H σ : ℝ} {s : ℕ}
    (hH : 1 < H) (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hbr : Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (𝓝 (1 - σ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
      ∃ T : Option (Fin s) → Fin (2 * s + 1) → ℝ,
        (∀ i, ∑ j, T i j = finiteSourceProfile H s (a n) (b n) i /
          ∑ k, finiteSourceProfile H s (a n) (b n) k) ∧
        (∀ j, ∑ i, T i j = finiteTargetProfile s (a n) (b n) j /
          ∑ k, finiteTargetProfile s (a n) (b n) k) ∧
        (∀ i j, 0 ≤ T i j) ∧
        (∀ i j, profileAllowed i j → ε < T i j) ∧
        (∀ i j, ¬profileAllowed i j → T i j = 0) := by
  classical
  let P := explicitProfileTransport H σ s
  let A := fun n i => finiteSourceProfile H s (a n) (b n) i /
    ∑ k, finiteSourceProfile H s (a n) (b n) k
  let B := fun n j => finiteTargetProfile s (a n) (b n) j /
    ∑ k, finiteTargetProfile s (a n) (b n) k
  obtain ⟨hA, hAp⟩ := sourceProfile_normalized_limit hH hσ hσ1 hs a b ha hb har hbr
  obtain ⟨hB, hBp⟩ := targetProfile_normalized_limit hσ hσ1 hs a b ha hb har hbr
  have hAr : ∀ i, Tendsto (fun n => A n i) atTop (𝓝 (∑ j, P i j)) := by
    intro i
    simpa only [P, explicitProfileTransport_row hH hσ hσ1 hs] using hA i
  have hBc : ∀ j, Tendsto (fun n => B n j) atTop (𝓝 (∑ i, P i j)) := by
    intro j
    simpa only [P, explicitProfileTransport_column] using hB j
  have hbalance : ∀ᶠ n : ℕ in atTop, ∑ i, A n i = ∑ j, B n j := by
    filter_upwards [hAp, hBp] with n hnA hnB
    dsimp only [A, B]
    rw [normalized_weights_sum _ hnA.ne', normalized_weights_sum _ hnB.ne']
  have ht := stable_positive_transport P (profileHub s) (profileParent hs) profileAllowed
    (explicitProfileTransport_pos hH hσ hσ1 hs) (explicitProfileTransport_zero hσ hσ1 hs)
    (profileHub_allowed s) (profileParent_allowed hs) A B hAr hBc hbalance
  let v : Option (Fin s) × Fin (2 * s + 1) → ℝ :=
    fun x => if profileAllowed x.1 x.2 then P x.1 x.2 / 2 else 1
  have hv : ∀ x ∈ (univ : Finset (Option (Fin s) × Fin (2 * s + 1))), 0 < v x := by
    intro x _
    dsimp only [v]
    split_ifs with hx
    · exact div_pos (explicitProfileTransport_pos hH hσ hσ1 hs x.1 x.2 hx) (by norm_num)
    · norm_num
  obtain ⟨ε, hε, hεv⟩ := finite_positive_lower_bound univ v hv
  refine ⟨ε, hε, ht.mono ?_⟩
  intro n hn
  obtain ⟨T, hTr, hTc, hTp, hTb, hTz⟩ := hn
  refine ⟨T, hTr, hTc, hTp, ?_, hTz⟩
  intro i j hij
  have hh := hεv (i, j) (mem_univ _)
  simp only [v, if_pos hij] at hh
  exact hh.trans_lt (hTb i j hij)

end Froberg
