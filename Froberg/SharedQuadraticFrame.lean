module

public import Froberg.CoordinateQuadraticProducts
public import Froberg.FrameDisjointOpen
public import Froberg.PrivateFrameNonzero
public import Froberg.PrivateFrameDetector

@[expose] public section

/-! The same quadratic output frame detects all outer symmetric products
and the complete private-power kernel. Both conditions hold on one
nonempty polynomial open of unrestricted frame coefficients. -/
noncomputable section
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K] {a z s b h H L : ℕ}

theorem shared_quadratic_frame_open
    (o : Fin L → Forms K h 1)
    (ho : LinearIndependent K (pairProducts (fun i => (o i).val)))
    (houter : H+(L+1).choose 2≤finrank K (Forms K h 2))
    (hh : 2≤h) (hprivate : H+(2*h-1)≤finrank K (Forms K h 2))
    (hs : 0<s) (ι : Fin b ↪ Fin z) :
    ∃ (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (w : Fin b → Fin h → K)
      (P : MvPolynomial (Fin (finrank K (Fin H → Forms K h 2))) K),
      (∀ i,w i≠0) ∧ (∃ x,eval x P≠0) ∧
      ∀ frame : Fin H → Forms K h 2,eval ((Module.finBasis K _).equivFun frame) P≠0 →
        let D := Submodule.span K (Set.range frame)
        ∃ T : Forms K h 2 →ₗ[K] (Fin (finrank K (Forms K h 2 ⧸ D)) → K),
          T.ker=D ∧
          LinearIndependent K (fun p => quadraticPolynomialDetector T
            (pairProducts (fun i => (o i).val) p)) ∧
          (privatePolynomialMap (a := a) (s := s) ι
            (fun i => (T.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
            Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))) := by
  classical
  let S := Submodule.span K (Set.range (quadraticPairForms o))
  obtain ⟨Q,hQ,hQgood⟩ := frame_disjoint_principal_open (K := K) (H := H)
    (fun _ : Unit => S) (by
      intro _
      simpa only [S,quadraticPairForms_span_finrank o ho] using houter)
  obtain ⟨e,w,P,hw,hP,hPgood⟩ := private_kernel_on_frame_open_nonzero
    (a := a) hh hprivate hs ι
  obtain ⟨x,hxP,hxQ⟩ := principal_opens_intersect hP hQ
  refine ⟨e,w,P*Q,hw,⟨x,?_⟩,?_⟩
  · simpa only [map_mul] using mul_ne_zero hxP hxQ
  intro frame hframe
  have hgood : eval ((Module.finBasis K _).equivFun frame) P≠0 ∧
      eval ((Module.finBasis K _).equivFun frame) Q≠0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hframe
  obtain ⟨T,hT,hker⟩ := hPgood frame hgood.1
  refine ⟨T,hT,?_,hker⟩
  have hmap : LinearIndependent K (T ∘ quadraticPairForms o) :=
    (quadraticPairForms_independent o ho).map (by
      rw [hT]
      exact (hQgood frame hgood.2 ()).symm)
  convert hmap using 1
  funext p
  change quadraticPolynomialDetector T (pairProducts (fun i => (o i).val) p)=T (quadraticPairForms o p)
  rw [←quadraticPairForms_val,quadraticPolynomialDetector_form]

end Froberg
