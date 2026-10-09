module

public import Froberg.PreparedFramePairCore
public import Froberg.UniformCountedPreparedBasic

@[expose] public section

/-! Both prepared frame opens use a single field-independent threshold. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg PreparedParameters Filter Module MvPolynomial
open scoped Topology

theorem eventually_uniform_counted_prepared_frames {d : ℕ} (hd : 3≤d) (hodd : d%2=1)
    (N₂ : ℕ) (hquad : ∀ h,N₂≤h → ∀ (K : Type) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop,∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ u : ℕ,∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x D≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) D≠0 →
            LinearIndependent K frame ∧
            ∀ U : Fin u → Forms K h d,PureFamilyAdmissible U →
              PreparedFramePairOpen hd n (f n) (e n) U frame := by
  filter_upwards [eventually_uniform_counted_basic_frames hd hodd N₂ hquad] with h hh
  intro k lo hk hkh hhpos upper a f e ha hc δ hδ hres u
  have hbase := hh k lo hk hkh hhpos upper a f e ha hc δ hδ hres u 0
  have hlarge := hh k lo hk hkh hhpos upper a f e ha hc δ hδ hres u 1
  filter_upwards [hbase,hlarge] with n hnbase hnlarge
  intro K _ _
  obtain ⟨D₀,hD₀,hgood₀⟩ := hnbase K
  obtain ⟨D₁,hD₁,hgood₁⟩ := hnlarge K
  obtain ⟨x,hx₀,hx₁⟩ := principal_opens_intersect hD₀ hD₁
  refine ⟨D₀*D₁,⟨x,?_⟩,?_⟩
  · simpa only [map_mul] using mul_ne_zero hx₀ hx₁
  intro frame hf
  have hfs : eval ((Module.finBasis K _).equivFun frame) D₀≠0 ∧
      eval ((Module.finBasis K _).equivFun frame) D₁≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hf
  obtain ⟨hfi,hb⟩ := hgood₀ frame hfs.1
  have hl := (hgood₁ frame hfs.2).2
  refine ⟨hfi,fun U hU => ?_⟩
  exact ⟨by simpa only [Nat.add_zero] using hb U hU,hl U hU⟩


end Froberg.PreparedTarget
