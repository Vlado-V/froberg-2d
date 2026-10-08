import Froberg.CountedRestoredCertificates
import Froberg.RestoredCertificateOpen
import Froberg.FrameEvenData

/-! Full restored certificates at the prescribed all-even counts. All
output frames and pure slots are selected after the scalar threshold. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]

def HasRestoredCertificateOpen {h m d q r f : ℕ} {J : Finset ℕ}
    {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
    (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r) : Prop :=
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  ∃ E : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
    (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) E≠0) ∧
    ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) E≠0 →
      RestoredCertificate hdp hd hO hJ heven idx slot p

theorem eventually_counted_restored_full_open {d : ℕ} (hd : 3≤d) (heven : d%2=0) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ added : ℕ,∀ᶠ n : ℕ in atTop,
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
  filter_upwards [eventually_frame_even_data (K := K) hd] with h hh
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres added
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hred := hh hdiv added e he
  have hback := eventually_counted_restored_odd_open (K := K) hd heven h added e he
  have hi := exact_counts_actual_restored_independent_open (K := K) hd heven hhpos upper a f e added hc
  have ho := exact_counts_all_even_restored_odd_open (K := K) hd heven hk hkh hhpos
    upper a f e ha hc hδ hres added
  filter_upwards [hred,hback,hi,ho] with n hnred hnback hni hno
  intro frame hframe slot hslot hu
  let hO := fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (allEvenCount d h n (e n+added)) (targetLayerOutput frame)) := finite_space hO
  obtain ⟨_,P,⟨p,hp⟩,hgood⟩ := hnred frame hframe
  obtain ⟨D,hD,hodd⟩ := hnback _ hO (Fintype.equivFin _).symm slot
  exact restored_certificate_principal_open (by omega) heven hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (fun j hj => by have := (mem_allEvenIndices.mp hj).1; omega)
    (Fintype.equivFin _).symm slot hslot p (hgood p hp) D hD hodd
    (hni _ hO slot) (hno _ hO slot) hu

end Froberg.PreparedParameters
