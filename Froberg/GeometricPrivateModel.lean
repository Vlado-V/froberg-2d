module

public import Froberg.UniformPrivateGrowth
public import Froberg.GenericVectorBaseChange
public import Froberg.OuterModelExistence

@[expose] public section

/-! A polynomial presentation realizing the uniform private-column estimate. -/
noncomputable section
namespace Froberg.PrivateColumns
open Filter Module OuterInjection AttachedMultiplication
open scoped Topology

 theorem eventually_exists_geometric_private_model {K L : Type*} [Field K] [Infinite K]
    [Field L] [Algebra K L]
    {k s h b : ℕ} (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 (limitingCoreFraction (s+1))))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-limitingCoreFraction (s+1))))
    (haz : ∀ n,a n+z n=n) :
    ∃ g : ℝ,0 < g ∧ ∀ᶠ n in atTop,
      ∃ (ι : Fin b ↪ Fin (z n)) (u : Labels k (a n) s ⊕ Fin b → Fin h → K),
      (∀ U : Finset (Labels k (a n) s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val)) ∧
      MixedExterior.UniversalMixedPosition u ∧
      (∀ c ≤ s+1, Function.Injective (multiplication (d := c) (attachedExponent ι) u)) ∧
      0 < finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))) ∧
      (finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))) : ℝ) ≤ g*(n : ℝ)^(s+1) ∧
      ∀ V : Submodule L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))),
        ((finrank L (PrivateTargetSpace ι (fun i j => algebraMap K L (u i j))) : ℝ)/finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j))))*finrank L V+
        g*(n : ℝ)^(s+1)*(min (finrank L V)
          (finrank L (PrivateSourceSpace ι (fun i j => algebraMap K L (u i j)))-finrank L V) : ℕ) ≤
        (finrank L (outerImage (d := s+1) (attachedExponent ι) (fun i j => algebraMap K L (u i j)) (attachedExponent_degree ι) V) : ℝ) := by
  classical
  have hex (n : ℕ) := MixedExterior.exists_universal_mixed_vectors
    (K := K) (α := Labels k (a n) s ⊕ Fin b) h
  choose u hu hm using hex
  let uL := fun n i j => algebraMap K L (u n i j)
  have huL n := MixedExterior.full_spark_map_coordinates (algebraMap K L) (u n) (hu n)
  have hmL n := (hm n).map_coordinates (algebraMap K L)
  obtain ⟨g,hg,hgrowth⟩ := uniform_private_outer_growth hk hs hh a z ha hz har hzr haz uL huL hmL
  have hdom := eventually_lt_of_normalized_limits
    (fun n : ℕ => (h : ℝ)*((n+s-1).choose s : ℝ))
    (fun n : ℕ => g*(n : ℝ)^(s+1)) (s+1) 0 g
    (exceptional_projection_error_lower_order (h : ℝ) s)
    (scaled_power_normalized_limit g (s+1)) hg
  refine ⟨g,hg,?_⟩
  filter_upwards [hgrowth,hdom,hz.eventually (eventually_ge_atTop b),
    eventually_gt_atTop (0 : ℕ)] with n hgn hdn hzn hn
  let ι : Fin b ↪ Fin (z n) := ⟨Fin.castLE hzn,Fin.castLE_injective hzn⟩
  have hnp : 0 < a n+z n := by rw [haz]; exact hn
  obtain ⟨hA,hG⟩ := hgn ι
  refine ⟨ι,u n,hu n,hm n,?_,hA,?_,?_⟩
  · intro c hc
    exact attached_multiplication_injective hs ι hh.ge (private_small_fiber_bound hk hs hh)
      (u n) (hu n) c hc
  · have he := private_source_dimension_add hk hs hh hnp ι (uL n) (huL n)
    have hle : finrank L (PrivateSourceSpace ι (uL n)) ≤
        finrank L (CoreSourceSpace (z := z n) (fun i => uL n (Sum.inl i))) := by omega
    have hd := hle.trans (core_source_dimension_le hnp (fun i => uL n (Sum.inl i)))
    conv_rhs at hd => rw [haz]
    have hdR : (finrank L (PrivateSourceSpace ι (uL n)) : ℝ) ≤
        (h : ℝ)*((n+s-1).choose s : ℝ) := by exact_mod_cast hd
    exact hdR.trans hdn.le
  · intro V
    simpa only [Nat.cast_min,Nat.cast_sub (Submodule.finrank_le V)] using hG V

end Froberg.PrivateColumns
