module

public import Froberg.UniformRestoredC4Selection
public import Froberg.RestoredThinBackground
public import Froberg.RestoredConcreteComparison
public import Froberg.RestoredFrameCore
public import Froberg.RestoredLeadingOpen
public import Froberg.ExactOuterBound

@[expose] public section

/-! The restored critical comparison has one scalar-dimension cutoff
before the field and common output frame are chosen. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen
open scoped Topology
attribute [local instance] tensorFormGroup
attribute [local irreducible] RestoredEndpointThin RestoredFormalQuadraticSeparation

theorem eventually_uniform_actual_restored_comparison {d k h lo : ℕ}
    (hd : 3≤d) (he : d%2=0) (hk : 0<k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
        RestoredFrameReady hd he n (f n) (e n) frame →
        Nonempty (LocalComparisonData K (h+n) d
          (adjacentCriticalCount upper (h+n) d) (criticalDefect K n d)) := by
  obtain ⟨G,C,ξ,hG,hC,hξ,hselect⟩ := uniform_exact_counts_restored_c4_selection
    hd he hk hh hhpos upper a f e ha hc hδ hreserve ((h+d-1).choose d)
  filter_upwards [hselect,hc,exact_counts_outer_below_degree hd upper a f e hc hξ,
    eventually_gt_atTop (0 : ℕ)] with n hn hcounts houter hnpos
  intro K _ _ _ frame hframe
  have hn := hn K
  let hO : ∀ j∈allEvenIndices d,targetLayerOutput frame j≤Forms K h j :=
    fun j _ => targetLayerOutput_homogeneous frame j
  let hJ : ∀ j∈allEvenIndices d,j≤d := fun j hj => (mem_allEvenIndices.mp hj).2.1
  let hev : ∀ j∈allEvenIndices d,j%2=0 := fun j hj => (mem_allEvenIndices.mp hj).2.2
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (actualRestoredCounts K d h n (e n) 0) (targetLayerOutput frame)) := finite_space hO
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (actualRestoredCounts K d h n (e n) 1) (targetLayerOutput frame)) := finite_space hO
  obtain ⟨A,hA,hAgood⟩ := hframe.certificates.1
  obtain ⟨B,hB,hBgood⟩ := hframe.certificates.2
  obtain ⟨L,hL,hLgood⟩ := restored_leading_principal_open hO hframe.leading
  obtain ⟨T,hT,hTgood⟩ := hframe.separation
  obtain ⟨v,hv⟩ := finite_basis_principal_intersection
    (V := RestoredOuterSpace n d (upperCount n d) (f n) (allEvenIndices d)
      (actualRestoredCounts K d h n (e n) 1) (targetLayerOutput frame))
    ![B,L,T] (by
      intro i
      fin_cases i
      · exact hB
      · exact hL
      · exact hT)
  have hD : ∃ v : RestoredOuterSpace n d (upperCount n d) (f n) (allEvenIndices d)
      (actualRestoredCounts K d h n (e n) 1) (targetLayerOutput frame),
      eval ((Module.finBasis K _).equivFun v) (B*L*T)≠0 :=
    ⟨v,by simpa [map_mul] using mul_ne_zero (mul_ne_zero (hv 0) (hv 1)) (hv 2)⟩
  have hcard : Fintype.card (ProductRows.LayerLabel (allEvenIndices d)
      (actualRestoredCounts K d h n (e n) 0))≤
      Fintype.card (ProductRows.LayerLabel (allEvenIndices d)
        (allEvenCount d h n (e n+(h+d-1).choose d))) := by
    simp only [actualRestoredCounts,actualRestoredPureCount,Nat.add_zero,finrank_forms K h d hhpos]
    exact le_rfl
  obtain ⟨p,hp,hbase,_,_,hthin,_,hchild⟩ := hn (allEvenIndices d)
    (actualRestoredCounts K d h n (e n) 0) (actualRestoredCounts K d h n (e n) 1)
    (targetLayerOutput frame) hO hJ hev (actualRestoredCounts_le hd)
    (actualRestoredSize K d h n (e n) 0) (actualRestoredIndex K d h n (e n) 0)
    (actualRestoredBaseSlot hd) (actualRestoredBaseSlot_positive hd) hcard
    (RestoredCertificate (by omega : 1≤d) he hO hJ hev
      (actualRestoredIndex K d h n (e n) 0) (actualRestoredBaseSlot hd))
    A (B*L*T) hA (fun p hp => ⟨hAgood p hp,(hAgood p hp).odd_exact,(hAgood p hp).upper_surjective⟩) hD
  have hparts : eval ((Module.finBasis K _).equivFun p) B≠0 ∧
      eval ((Module.finBasis K _).equivFun p) L≠0 ∧
      eval ((Module.finBasis K _).equivFun p) T≠0 := by
    simpa only [map_mul,mul_ne_zero_iff,and_assoc] using hp
  have hlarge := hBgood p hparts.1
  have hleading := hLgood p hparts.2.1
  have hsep := hTgood p hparts.2.2
  have hthin' := restored_endpoint_thin_background (by omega : 1≤d) he hO hJ hev
    (actualRestoredIndex K d h n (e n) 0) (actualRestoredBaseSlot hd)
    (actualRestoredBaseSlot_positive hd) (ξ*(n : ℝ)^d)
    (restoredRestrictCounts (actualRestoredCounts_le hd) p) hthin
  apply exists_critical_comparison_of_restored_background
    hnpos (by omega : 1≤d) he upper hO hJ hev
    (fun j hj => by have H := (mem_allEvenIndices.mp hj).1; omega)
    (fun j _ hj => actualRestoredCounts_positive_lt hd 1 j hj)
    (actualRestoredCounts_le hd) (actualRestoredExtraLayer hd)
    (actualRestoredExtraLayer_not_old hd) (actualRestoredExtraLayer_cover hd)
    (actualRestoredIndex K d h n (e n) 0) (actualRestoredIndex K d h n (e n) 1)
    (actualRestoredBaseSlot hd) (actualRestoredBaseSlot_positive hd) p hbase hlarge hleading
    (actualRestored_final_card hd hhpos he hcounts) (C*(n : ℝ)^d) hchild
    (ξ*(n : ℝ)^d) houter hthin'
  unfold RestoredFormalQuadraticSeparation at hsep
  exact hsep

/-- Eventual common-frame data gives the critical comparison at every
sufficiently large scalar dimension. -/
theorem uniform_actual_restored_comparison_of_eventual_frames {d k h lo : ℕ}
    (hd : 3≤d) (he : d%2=0) (hk : 0<k)
    (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (hframes : ∀ᶠ n : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∃ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
        RestoredFrameReady hd he n (f n) (e n) frame) :
    ∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K] [IsAlgClosed K],
      Nonempty (LocalComparisonData K (h+n) d
      (adjacentCriticalCount upper (h+n) d) (criticalDefect K n d)) := by
  filter_upwards [eventually_uniform_actual_restored_comparison hd he hk hh hhpos
    upper a f e ha hc hδ hreserve,hframes] with n hn hf
  intro K _ _ _
  obtain ⟨frame,hframe⟩ := hf K
  exact hn K frame hframe

end Froberg.PreparedParameters
