module

public import Froberg.FieldUniformPrivateGrowth
public import Froberg.PrivateGenericModel

@[expose] public section

/-! The private model and its coefficient open with a common field-independent
growth constant and a common numerical threshold. -/
noncomputable section
namespace Froberg.PrivateColumns
open Filter Module MvPolynomial OuterInjection VectorExpansionOpen AttachedMultiplication
open scoped Topology

theorem eventually_field_uniform_private_strict_open
    {k s h b : ℕ} (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 (limitingCoreFraction (s+1))))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-limitingCoreFraction (s+1))))
    (haz : ∀ n,a n+z n=n) :
    ∃ G : ℝ,0 < G ∧ ∀ᶠ n in atTop,∀ (K : Type) [Field K] [Infinite K],
      ∃ D : MvPolynomial (VectorParameters.Index h (a n+z n) s
        (Fintype.card (Labels k (a n) s ⊕ Fin b))) K,
        (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
          StrictModel (VectorParameters.generators p) (s+1) (G*(n : ℝ)^(s+1)) := by
  classical
  obtain ⟨G,hG,hgrowth⟩ := field_uniform_private_outer_growth (b := b)
    hk hs hh a z ha hz har hzr haz
  have hdom := eventually_lt_of_normalized_limits
    (fun n : ℕ => (h : ℝ)*((n+s-1).choose s : ℝ))
    (fun n : ℕ => G*(n : ℝ)^(s+1)) (s+1) 0 G
    (exceptional_projection_error_lower_order (h : ℝ) s)
    (scaled_power_normalized_limit G (s+1)) hG
  refine ⟨G,hG,?_⟩
  filter_upwards [hgrowth,hdom,hz.eventually (eventually_ge_atTop b),
    ha.eventually (eventually_gt_atTop 0),eventually_gt_atTop (0 : ℕ)]
    with n hgn hdn hzn han hn
  intro K _ _
  obtain ⟨u,hu,hm⟩ := MixedExterior.exists_universal_mixed_vectors
    (K := K) (α := Labels k (a n) s ⊕ Fin b) h
  let ι : Fin b ↪ Fin (z n) := ⟨Fin.castLE hzn,Fin.castLE_injective hzn⟩
  let uL := fun i j => algebraMap K (AlgebraicClosure K) (u i j)
  have huL := MixedExterior.full_spark_map_coordinates (algebraMap K (AlgebraicClosure K)) u hu
  have hmL := hm.map_coordinates (algebraMap K (AlgebraicClosure K))
  obtain ⟨hA,hgrow⟩ := hgn (AlgebraicClosure K) uL huL hmL ι
  have hnp : 0 < a n+z n := by rw [haz]; exact hn
  have hc : 0 < Fintype.card (Labels k (a n) s ⊕ Fin b) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Sum.inl (⟨0,hk⟩,Sym.replicate s ⟨0,han⟩)⟩
  have hGA : (finrank (AlgebraicClosure K) (PrivateSourceSpace ι uL) : ℝ) ≤ G*(n : ℝ)^(s+1) := by
    have he := private_source_dimension_add hk hs hh hnp ι uL huL
    have hle : finrank (AlgebraicClosure K) (PrivateSourceSpace ι uL) ≤
        finrank (AlgebraicClosure K) (CoreSourceSpace (z := z n) (fun i => uL (Sum.inl i))) := by omega
    have hd := hle.trans (core_source_dimension_le hnp (fun i => uL (Sum.inl i)))
    conv_rhs at hd => rw [haz]
    have hdR : (finrank (AlgebraicClosure K) (PrivateSourceSpace ι uL) : ℝ) ≤
        (h : ℝ)*((n+s-1).choose s : ℝ) := by exact_mod_cast hd
    exact hdR.trans hdn.le
  apply private_open_of_geometric_growth (L := AlgebraicClosure K)
    hk hs hh hnp hc ι u hu (G*(n : ℝ)^(s+1)) hA hGA
  intro V
  simpa only [Nat.cast_min,Nat.cast_sub (Submodule.finrank_le V)] using hgrow V

end Froberg.PrivateColumns
