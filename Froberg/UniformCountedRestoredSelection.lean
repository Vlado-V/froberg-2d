module

public import Froberg.RestoredFrameCore
public import Froberg.UniformCountedRestoredFrames
public import Froberg.UniformSharedQuadraticFrame
public import Froberg.UniformRestoredQuadraticFormalOpen
public import Froberg.FieldUniformFrameEvenData

@[expose] public section

/-! The complete restored frame is chosen after thresholds uniform in the field. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial

theorem eventually_uniform_counted_restored_frame_ready {d : ℕ} (hd : 3≤d) (heven : d%2=0)
    (N₂ : ℕ) (hquad : ∀ h,N₂≤h → ∀ (K : Type) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
        ∃ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
          RestoredFrameReady hd heven n (f n) (e n) frame := by
  filter_upwards [eventually_uniform_counted_restored_frames hd heven N₂ hquad,
    eventually_uniform_frame_even_data hd,
    eventually_uniform_counted_shared_quadratic_frame hd] with h hframes hevenData hshared
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
  have hf := hframes hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
  have hl := hevenData hdiv ((h+d-1).choose d+1) e
    (hc.mono fun n hn => hn.quadratic_upper)
  have hs := uniform_exact_counts_restored_frame_quadratic_open hd heven hhpos upper a f e 1 hc
  filter_upwards [hf,hl,hs] with n hfn hln hsn
  intro K _ _
  obtain ⟨o,ho,hshared⟩ := hshared K
  let EvenData (u : ℕ) : Prop :=
    ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
      LinearIndependent K frame → FrameEvenData d n (e n+(u+1)) frame
  have huK : (h+d-1).choose d=actualRestoredPureCount K d h :=
    (finrank_forms K h d hhpos).symm
  have hln : EvenData (actualRestoredPureCount K d h) :=
    Eq.mp (congrArg EvenData huK) (show EvenData ((h+d-1).choose d) from hln K)
  obtain ⟨D,hD,hDgood⟩ := hfn K
  obtain ⟨basis,w,P,hw,hP,hPgood⟩ := hshared n 0 0 (Function.Embedding.refl _)
  obtain ⟨x,hxD,hxP⟩ := principal_opens_intersect hD hP
  let frame := (Module.finBasis K (Fin (quadraticOutputDimension d h) → Forms K h 2)).equivFun.symm x
  have hDframe : eval ((Module.finBasis K _).equivFun frame) D≠0 := by
    simpa only [frame,LinearEquiv.apply_symm_apply] using hxD
  have hPframe : eval ((Module.finBasis K _).equivFun frame) P≠0 := by
    simpa only [frame,LinearEquiv.apply_symm_apply] using hxP
  obtain ⟨hfi,hpair⟩ := hDgood frame hDframe
  obtain ⟨T,hker,hoT,_⟩ := hPgood frame hPframe
  refine ⟨frame,⟨hfi,hpair,?_,?_⟩⟩
  · have hh := (hln frame hfi).1
    have hcounts : allEvenCount d h n (e n+(actualRestoredPureCount K d h+1))=
        actualRestoredCounts K d h n (e n) 1 := by
      simp only [actualRestoredCounts,Nat.add_assoc]
    exact (leading_witnesses_congr_counts (targetLayerOutput frame) hcounts).mp hh
  · exact hsn K frame (actualRestoredEnlargedSlot hd) _ T hker o hoT


end Froberg.PreparedParameters
