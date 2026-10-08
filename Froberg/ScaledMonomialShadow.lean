import Froberg.UniformMonomialShadow

/-! The shadow inequality is invariant under multiplying all capacities
by the fixed block multiplicity. -/
noncomputable section
namespace Froberg
open Finset MonomialExpansion

lemma scale_shadow_inequality {I J : Type*} [Fintype I] [Fintype J]
    (d : I → ℝ) (c : J → ℝ) (R : I → J → Prop) (A T g K : ℝ) (hK : 0 < K)
    (hbase : ∀ (l : I → ℝ) (b : J → ℝ),
      (∀ i, 0 ≤ l i ∧ l i ≤ d i) →
      (∀ i j, R i j → min (c j) (l i) ≤ b j) →
      (T/A) * (∑ i, l i) + g*(T/A)*min (∑ i, l i) (A-∑ i, l i) ≤ ∑ j, b j)
    (l : I → ℝ) (b : J → ℝ)
    (hl : ∀ i, 0 ≤ l i ∧ l i ≤ K*d i)
    (hb : ∀ i j, R i j → min (K*c j) (l i) ≤ b j) :
    (T/A)*(∑ i, l i) + g*(T/A)*min (∑ i, l i) (K*A-∑ i, l i) ≤ ∑ j, b j := by
  have hu (i : I) : 0 ≤ l i / K ∧ l i / K ≤ d i := by
    refine ⟨div_nonneg (hl i).1 hK.le, (div_le_iff₀ hK).mpr ?_⟩
    simpa only [mul_comm K] using (hl i).2
  have hv (i : I) (j : J) (hij : R i j) : min (c j) (l i / K) ≤ b j / K := by
    have hh := div_le_div_of_nonneg_right (hb i j hij) hK.le
    rw [← min_div_div_right hK.le] at hh
    have he : K*c j/K=c j := by field_simp
    rwa [he] at hh
  have hh := hbase (fun i => l i/K) (fun j => b j/K) hu hv
  simp only [← sum_div] at hh
  have he : A-(∑ i, l i)/K=(K*A-∑ i, l i)/K := by field_simp
  rw [he,min_div_div_right hK.le] at hh
  calc
    _ = K * ((T/A)*((∑ i, l i)/K)+g*(T/A)*(min (∑ i, l i) (K*A-∑ i, l i)/K)) := by
      field_simp
      <;> ring
    _ ≤ K * ((∑ j, b j)/K) := mul_le_mul_of_nonneg_left hh hK.le
    _ = _ := by field_simp

open Filter
open scoped Topology

theorem uniform_scaled_monomial_shadow {σ : ℝ} {s : ℕ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (hs : 0 < s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 σ))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ) / n) atTop (𝓝 (1-σ)))
    (haz : ∀ n, a n + z n = n) (K : ℝ) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      ∀ (ell : (Σ i, SourceMonomialFiber (a n) (z n) s i) → ℝ)
        (b : (Σ j, TargetMonomialFiber (a n) (z n) s j) → ℝ),
      (∀ α, 0 ≤ ell α ∧ ell α ≤ K*profileSourceCapacity (profileAmbientCapacity s) α.1) →
      (∀ α β, OuterInjection.joinParts α.2.1.val α.2.2.val ≤
        OuterInjection.joinParts β.2.1.val β.2.2.val →
        min (K*profileTargetCapacity s β.1) (ell α) ≤ b β) →
      let A := ∑ i, finiteSourceProfile (profileAmbientCapacity s) s (a n) (z n) i
      let T := ∑ j, finiteTargetProfile s (a n) (z n) j
      (T/A) * (∑ α, ell α) + c * (T/A) *
        min (∑ α, ell α) (K*A-∑ α, ell α) ≤ ∑ β, b β := by
  obtain ⟨c,hc,hev⟩ := uniform_monomial_shadow hσ hσ1 hs a z ha hz har hzr haz
  refine ⟨c,hc,hev.mono ?_⟩
  intro n hn ell b hell hb
  exact scale_shadow_inequality _ _ _ _ _ c K hK hn ell b hell hb

end Froberg
