import Froberg.CountedRestoredFullOpen
import Froberg.CountedUpperFrames
import Froberg.RestoredUpperCountExtension
import Froberg.ActualRestoredSlots

/-! The same quadratic output frame admits full restored certificates for
both the critical family and its one-column enlargement. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [CharZero K]

def RestoredFramePairOpen {d h : ℕ} (hd : 3≤d) (he : d%2=0) (n f e : ℕ)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2) : Prop :=
  HasRestoredCertificateOpen (m := n) (f := f) (by omega : 1≤d) he
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (actualRestoredIndex K d h n e 0) (actualRestoredBaseSlot hd) ∧
  HasRestoredCertificateOpen (m := n) (f := f) (by omega : 1≤d) he
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (actualRestoredIndex K d h n e 1) (actualRestoredEnlargedSlot hd)

theorem eventually_counted_restored_frames {d : ℕ} (hd : 3≤d) (heven : d%2=0) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ᶠ n : ℕ in atTop,
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x D≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) D≠0 →
            LinearIndependent K frame ∧ RestoredFramePairOpen hd heven n (f n) (e n) frame := by
  filter_upwards [eventually_counted_restored_full_open (K := K) hd heven,
    eventually_indexed_upper_frames (K := K) hd] with h hfull hupper
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
  let u := finrank K (Forms K h d)
  have hbase := hfull hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres u
  have hlarge := hfull hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres (u+1)
  have hu := hupper f (exact_conditions_outer_limit hd upper a f e hc)
  filter_upwards [hbase,hlarge,hu,hc] with n hnbase hnlarge hnu hnc
  obtain ⟨D,hD,hframe⟩ := hnu (e n) hnc.quadratic_lower
  refine ⟨D,hD,?_⟩
  intro frame hf
  obtain ⟨hfi,hfw⟩ := hframe frame hf
  refine ⟨hfi,?_⟩
  let U : Fin u → Forms K h d := Module.finBasis K (Forms K h d)
  have hU : PureFamilyAdmissible U := pureFamilyAdmissible_of_span_top U
    (Module.finBasis K (Forms K h d)).span_eq
  have hwb := (hfw u (upperCount n d) U hU).restored_upper_open hd heven frame U
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
