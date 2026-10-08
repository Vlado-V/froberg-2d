import Froberg.ScalarReserveCount

/-! A common positive capacity for layered covector incidence. All nuisance
counts are lower order, while both available capacities have positive density. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

theorem layered_capacity_eventually {d : ℕ} (hd : 0<d)
    (H a q C : ℕ → ℕ) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ)
    (hH : Tendsto (fun n : ℕ => (H n : ℝ)/(n : ℝ)^d) atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ => (a n : ℝ)/(n : ℝ)^d) atTop (𝓝 0))
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop (𝓝 0))
    (hC : Tendsto (fun n : ℕ => (C n : ℝ)/(n : ℝ)^d) atTop (𝓝 c)) :
    ∃ (L : ℕ → ℕ) (ξ : ℝ),0<ξ ∧ ∀ᶠ n : ℕ in atTop,
      0<L n ∧ L n≤C n ∧ L n≤⌊δ*(n : ℝ)^d⌋₊ ∧
      2*(H n+a n+q n)+1≤L n ∧
      ∀ k : ℕ,1≤k → 2*⌈ξ*(n : ℝ)^d*(k : ℝ)⌉₊≤L n*k := by
  let l := min c δ/2
  have hl : 0<l := div_pos (lt_min hc hδ) (by norm_num)
  have hlc : l<c := by have := min_le_left c δ;dsimp [l];linarith
  have hlδ : l<δ := by have := min_le_right c δ;dsimp [l];linarith
  let L : ℕ → ℕ := fun n => ⌊l*(n : ℝ)^d⌋₊
  have hL : Tendsto (fun n : ℕ => (L n : ℝ)/(n : ℝ)^d) atTop (𝓝 l) :=
    floor_normalized_limit _ hd _ (Eventually.of_forall fun n => by positivity)
      (scaled_power_normalized_limit l d)
  have hM : Tendsto (fun n : ℕ => (⌊δ*(n : ℝ)^d⌋₊ : ℝ)/(n : ℝ)^d) atTop (𝓝 δ) :=
    floor_normalized_limit _ hd _ (Eventually.of_forall fun n => by positivity)
      (scaled_power_normalized_limit δ d)
  have hB : Tendsto (fun n : ℕ => ((2*(H n+a n+q n)+1 : ℕ) : ℝ)/(n : ℝ)^d)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)^d) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop d hd)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      add_div,mul_div_assoc,zero_add,mul_zero] using (((hH.add ha).add hq).const_mul 2).add h1
  have hLC := eventually_lt_of_normalized_limits _ _ d _ _ hL hC hlc
  have hLM := eventually_lt_of_normalized_limits _ _ d _ _ hL hM hlδ
  have hBL := eventually_lt_of_normalized_limits _ _ d _ _ hB hL hl
  have hlow := eventually_lt_of_normalized_limits _ _ d _ _
    (scaled_power_normalized_limit (l/2) d) hL (by linarith)
  let ξ := l/8
  have hξ : 0<ξ := div_pos hl (by norm_num)
  have hbig := (nat_power_tendsto_atTop d hd).eventually (eventually_ge_atTop (1/ξ))
  refine ⟨L,ξ,hξ,?_⟩
  filter_upwards [hLC,hLM,hBL,hlow,hbig] with n hLC hLM hBL hlow hbig
  have hLC' : L n<C n := by exact_mod_cast hLC
  have hLM' : L n<⌊δ*(n : ℝ)^d⌋₊ := by exact_mod_cast hLM
  have hBL' : 2*(H n+a n+q n)+1<L n := by exact_mod_cast hBL
  refine ⟨by omega,hLC'.le,hLM'.le,hBL'.le,?_⟩
  intro k hk
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0 : ℝ)≤k := Nat.cast_nonneg k
  have hn0 : (0 : ℝ)≤(n : ℝ)^d := by positivity
  have hx : 1≤ξ*(n : ℝ)^d := by
    have hh := (div_le_iff₀ hξ).mp hbig
    nlinarith
  have hxk : 1≤ξ*(n : ℝ)^d*(k : ℝ) := by nlinarith
  have hceil := Nat.ceil_lt_add_one (show 0≤ξ*(n : ℝ)^d*(k : ℝ) by positivity)
  have hmul := mul_le_mul_of_nonneg_right hlow.le hk0
  have hres : (2 : ℝ)*(⌈ξ*(n : ℝ)^d*(k : ℝ)⌉₊ : ℝ)≤(L n : ℝ)*(k : ℝ) := by
    dsimp [ξ] at *
    nlinarith
  exact_mod_cast hres

end Froberg
