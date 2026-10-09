module

public import Froberg.RestoredFramePairCore
public import Froberg.RestoredUpperCountExtension
public import Froberg.UniformCountedRestoredFull
public import Froberg.UniformCountedUpperFrames

@[expose] public section

/-! Both restored frame opens have a common threshold independent of the field. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial
open scoped Topology

theorem eventually_uniform_counted_restored_frames {d : ℕ} (hd : 3≤d) (heven : d%2=0)
    (N₂ : ℕ) (hquad : ∀ h,N₂≤h → ∀ (K : Type) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x D≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) D≠0 →
            LinearIndependent K frame ∧ RestoredFramePairOpen hd heven n (f n) (e n) frame := by
  filter_upwards [eventually_uniform_counted_restored_full_open hd heven,
    eventually_uniform_indexed_upper_frames hd N₂ hquad] with h hfull hupper
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
  let u := (h+d-1).choose d
  have hbase := hfull hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres u
  have hlarge := hfull hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres (u+1)
  have hu := hupper f (exact_conditions_outer_limit hd upper a f e hc)
  filter_upwards [hbase,hlarge,hu,hc] with n hnbase hnlarge hnu hnc
  intro K _ _
  have huK : u=finrank K (Forms K h d) := (finrank_forms K h d hhpos).symm
  let Upgrade (added : ℕ) : Prop :=
    ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
      LinearIndependent K frame →
    ∀ slot : Fin (finrank K (Forms K h d)) →
      Fin (Fintype.card (Label (upperCount n d) (allEvenIndices d)
        (allEvenCount d h n (e n+added)))),
    (∀ i,0<degree ((Fintype.equivFin _).symm (slot i))) →
    HasRestoredUpperOpen (m := n) (f := f n) (by omega : 1≤d) heven
      (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
      (fun j hj => (mem_allEvenIndices.mp hj).2.1)
      (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot →
    HasRestoredCertificateOpen (m := n) (f := f n) (by omega : 1≤d) heven
      (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
      (fun j hj => (mem_allEvenIndices.mp hj).2.1)
      (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot
  have hnbase : Upgrade (finrank K (Forms K h d)) :=
    Eq.mp (congrArg Upgrade huK) (show Upgrade u from hnbase K)
  have hnlarge : Upgrade (finrank K (Forms K h d)+1) :=
    Eq.mp (congrArg (fun v => Upgrade (v+1)) huK) (show Upgrade (u+1) from hnlarge K)
  obtain ⟨D,hD,hframe⟩ := hnu K (e n) hnc.quadratic_lower
  refine ⟨D,hD,?_⟩
  intro frame hf
  obtain ⟨hfi,hfw⟩ := hframe frame hf
  refine ⟨hfi,?_⟩
  let U : Fin (finrank K (Forms K h d)) → Forms K h d := Module.finBasis K (Forms K h d)
  have hU : PureFamilyAdmissible U := by
    have hspan : Submodule.span K (Set.range U)=⊤ :=
      (Module.finBasis K (Forms K h d)).span_eq
    refine ⟨?_,fun _ => hspan⟩
    rw [hspan]
    apply Submodule.map_injective_of_injective (f := (Forms K h (d+1)).subtype)
      (Submodule.injective_subtype _)
    rw [graded_flip_image_polynomial,Submodule.map_top,Submodule.range_subtype,
      Submodule.map_top,Submodule.range_subtype,forms_mul_forms]
  have hwb := (hfw (finrank K (Forms K h d)) (upperCount n d) U hU).restored_upper_open hd heven frame U
    (actualRestoredIndex K d h n (e n) 0)
  have hwl := hwb.extend_counts (by omega : 1≤d) heven
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (actualRestoredCounts_le hd)
    (actualRestoredIndex K d h n (e n) 0) (actualRestoredIndex K d h n (e n) 1)
    (actualRestoredBaseSlot hd)
  refine ⟨?_,?_⟩
  · exact hnbase frame hfi (actualRestoredBaseSlot hd) (actualRestoredBaseSlot_positive hd) hwb
  · exact hnlarge frame hfi (actualRestoredEnlargedSlot hd) (actualRestoredEnlargedSlot_positive hd) hwl


end Froberg.PreparedParameters
