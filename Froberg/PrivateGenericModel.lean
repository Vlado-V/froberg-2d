import Froberg.PrivateModelOpen
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The uniform B.2 private-column construction on a nonempty open in the
full coefficient space, with actual strict growth and scalar maximal rank. -/
noncomputable section
namespace Froberg.PrivateColumns
open Filter Module MvPolynomial OuterInjection VectorExpansionOpen
open scoped Topology

 theorem eventually_private_strict_open {K : Type*} [Field K] [Infinite K]
    {k s h b : ℕ} (hk : 0 < k) (hs : 2 ≤ s) (hh : h=k*(2*s+1).choose s)
    (a z : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hz : Tendsto z atTop atTop)
    (har : Tendsto (fun n : ℕ => (a n : ℝ)/n) atTop (𝓝 (limitingCoreFraction (s+1))))
    (hzr : Tendsto (fun n : ℕ => (z n : ℝ)/n) atTop (𝓝 (1-limitingCoreFraction (s+1))))
    (haz : ∀ n,a n+z n=n) :
    ∃ G : ℝ,0 < G ∧ ∀ᶠ n in atTop,
      ∃ D : MvPolynomial (VectorParameters.Index h (a n+z n) s
        (Fintype.card (Labels k (a n) s ⊕ Fin b))) K,
        (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
          StrictModel (VectorParameters.generators p) (s+1) (G*(n : ℝ)^(s+1)) := by
  obtain ⟨G,hG,hmodels⟩ := eventually_exists_geometric_private_model
    (K := K) (L := AlgebraicClosure K) hk hs hh a z ha hz har hzr haz
  refine ⟨G,hG,?_⟩
  filter_upwards [hmodels,ha.eventually (eventually_gt_atTop 0)] with n hn han
  obtain ⟨ι,u,hu,hm,hi,hA,hGA,hgrow⟩ := hn
  have hnp : 0 < a n+z n := by omega
  have hc : 0 < Fintype.card (Labels k (a n) s ⊕ Fin b) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Sum.inl (⟨0,hk⟩,Sym.replicate s ⟨0,han⟩)⟩
  exact private_open_of_geometric_growth (L := AlgebraicClosure K)
    hk hs hh hnp hc ι u hu (G*(n : ℝ)^(s+1)) hA hGA hgrow

end Froberg.PrivateColumns
