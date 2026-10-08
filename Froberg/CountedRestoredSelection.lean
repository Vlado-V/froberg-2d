import Froberg.CountedRestoredFrames
import Froberg.CountedSharedQuadraticFrame
import Froberg.RestoredQuadraticFormalOpen

/-! All frame-dependent hypotheses of the even-degree comparison hold
for one common output frame at each sufficiently large scalar dimension. -/
noncomputable section
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial
variable {K : Type} [Field K] [CharZero K]

structure RestoredFrameReady {d h : ℕ} (hd : 3≤d) (he : d%2=0) (n f e : ℕ)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2) : Prop where
  independent : LinearIndependent K frame
  certificates : RestoredFramePairOpen hd he n f e frame
  leading : ∀ j : allEvenIndices d,∃ p : Space n d (upperCount n d) (allEvenIndices d)
    (actualRestoredCounts K d h n e 1) (targetLayerOutput frame),LinearIndependent K (p.2 j)
  separation : HasRestoredFormalQuadraticOpen (m := n) (f := f) (by omega : 1≤d) he
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (actualRestoredIndex K d h n e 1) (actualRestoredEnlargedSlot hd)

theorem eventually_counted_restored_frame_ready {d : ℕ} (hd : 3≤d) (heven : d%2=0) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ᶠ n : ℕ in atTop,
        ∃ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
          RestoredFrameReady hd heven n (f n) (e n) frame := by
  filter_upwards [eventually_counted_restored_frames (K := K) hd heven,
    eventually_frame_even_data (K := K) hd,
    eventually_counted_shared_quadratic_frame (K := K) hd] with h hframes hevenData hshared
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
  have hf := hframes hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
  have hl := hevenData hdiv (actualRestoredPureCount K d h+1) e
    (hc.mono fun n hn => hn.quadratic_upper)
  have hs := exact_counts_restored_frame_quadratic_open (K := K) hd heven hhpos upper a f e 1 hc
  obtain ⟨o,ho,hshared⟩ := hshared
  filter_upwards [hf,hl,hs] with n hfn hln hsn
  obtain ⟨D,hD,hDgood⟩ := hfn
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
  · exact hsn frame (actualRestoredEnlargedSlot hd) _ T hker o hoT

end Froberg.PreparedParameters
