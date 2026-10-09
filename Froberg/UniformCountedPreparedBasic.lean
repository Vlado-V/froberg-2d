module

public import Froberg.PreparedBasicCore
public import Froberg.UniformCountedUpperFrames
public import Froberg.UniformCountedIndependence
public import Froberg.FieldUniformCountedCertificates

@[expose] public section

/-! Actual-count basic frame opens with both bounds chosen before the field. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial PreparedParameters
open scoped Topology

theorem eventually_uniform_counted_basic_frames {d : ℕ} (hd : 3 ≤ d) (hdodd : d%2=1)
    (N₂ : ℕ) (hquad : ∀ h,N₂≤h → ∀ (K : Type) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop,∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ (u extra : ℕ),∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x D≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) D≠0 →
            LinearIndependent K frame ∧
            ∀ U : Fin u → Forms K h d,PureFamilyAdmissible U →
              HasBasicOpen (m := n) (q := upperCount n d) (f := f n)
                (counts := allEvenCount d h n (e n+extra)) (by omega : 0<d)
                (fun j _ => targetLayerOutput_homogeneous frame j)
                (fun j hj => (mem_allEvenIndices.mp hj).2.1) U := by
  filter_upwards [eventually_uniform_indexed_upper_frames hd N₂ hquad] with h hh
  intro k lo hk hkh hhpos upper a f e ha hc δ hδ hres u extra
  have hi := uniform_exact_counts_all_even_independent_open (u := u) hd hhpos upper a f e hc extra
  have ho := uniform_exact_counts_all_even_odd_open (u := u) hd hdodd hk hkh hhpos
    upper a f e ha hc hδ hres extra
  have hupper := hh f (exact_conditions_outer_limit hd upper a f e hc)
  filter_upwards [hi,ho,hupper,hc] with n hnI hnO hnU hnC
  intro K _ _
  obtain ⟨D,hD,hframe⟩ := hnU K (e n+extra) (hnC.quadratic_lower.trans (by exact_mod_cast Nat.le_add_right (e n) extra))
  refine ⟨D,hD,?_⟩
  intro frame hf
  obtain ⟨hfi,hfw⟩ := hframe frame hf
  refine ⟨hfi,fun U hU => ?_⟩
  exact (hfw u (upperCount n d) U hU).all_even_basic_open hd frame U
    (hnI K _ _) (hnO K _ _)


end Froberg.PreparedTarget
