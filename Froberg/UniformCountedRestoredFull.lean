module

public import Froberg.CountedRestoredFullOpen
public import Froberg.UniformRestoredIndependence
public import Froberg.UniformRestoredBackground
public import Froberg.FieldUniformFrameEvenData
public import Froberg.FieldUniformCountedCertificates

@[expose] public section

/-! All restored certificate thresholds precede the field and frame. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial

theorem eventually_uniform_counted_restored_full_open {d : ℕ} (hd : 3≤d) (heven : d%2=0) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ added : ℕ,∀ᶠ n : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
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
          (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot := by
  filter_upwards [eventually_uniform_frame_even_data hd] with h hh
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres added
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hred := hh hdiv added e he
  have hback := eventually_uniform_counted_restored_odd_open hd heven h added e he
  have hi := uniform_exact_counts_actual_restored_independent_open hd heven hhpos upper a f e added hc
  have ho := uniform_exact_counts_all_even_restored_odd_open hd heven hk hkh hhpos
    upper a f e ha hc hδ hres added
  filter_upwards [hred,hback,hi,ho] with n hnred hnback hni hno
  intro K _ _ frame hframe slot hslot hu
  let hO := fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (allEvenCount d h n (e n+added)) (targetLayerOutput frame)) := finite_space hO
  obtain ⟨_,P,⟨p,hp⟩,hgood⟩ := hnred K frame hframe
  obtain ⟨D,hD,hodd⟩ := hnback K _ hO (Fintype.equivFin _).symm slot
  exact restored_certificate_principal_open (by omega) heven hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (fun j hj => by have := (mem_allEvenIndices.mp hj).1; omega)
    (Fintype.equivFin _).symm slot hslot p (hgood p hp) D hD hodd
    (hni K _ hO slot) (hno K _ hO slot) hu


end Froberg.PreparedParameters
