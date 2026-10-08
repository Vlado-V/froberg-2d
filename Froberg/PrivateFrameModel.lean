import Froberg.PrivateFrameOpen
import Froberg.GeneralLinearColumns
import Froberg.PrivateKoszulKernel

/-! The exact private-power kernel holds for a general quadratic frame.
The detector has kernel precisely the span of that same frame. -/
noncomputable section
namespace Froberg.PrivateColumns
open Module MvPolynomial
variable {K : Type*} [Field K] [Infinite K] {a z s b h H : ℕ}

theorem private_kernel_on_frame_open (hh : 2≤h)
    (hcap : H+(2*h-1)≤finrank K (Forms K h 2)) (hs : 0<s)
    (ι : Fin b ↪ Fin z) :
    ∃ (e : (Fin h → K) ≃ₗ[K] Forms K h 1) (w : Fin b → Fin h → K)
      (P : MvPolynomial (Fin (finrank K (Fin H → Forms K h 2))) K),
      (∃ x,eval x P≠0) ∧
      ∀ frame : Fin H → Forms K h 2,eval ((Module.finBasis K _).equivFun frame) P≠0 →
        let D := Submodule.span K (Set.range frame)
        ∃ L : Forms K h 2 →ₗ[K] (Fin (finrank K (Forms K h 2 ⧸ D)) → K),
          L.ker=D ∧
          (privatePolynomialMap (a := a) (s := s) ι
            (fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
            Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))) := by
  let e : (Fin h → K) ≃ₗ[K] Forms K h 1 := LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_forms K h 1 (by omega)]
    simp)
  obtain ⟨v,hv,hpair⟩ := exists_pairwise_independent_linear_columns (K := K) hh b
  let w : Fin b → Fin h → K := fun i => e.symm (v i)
  have hw (i : Fin b) : w i≠0 := by
    intro hz
    apply hv i
    have he := congrArg e hz
    simpa only [w,LinearEquiv.apply_symm_apply,map_zero] using he
  choose dual hdual using fun i => Module.Projective.exists_dual_eq_one K (hw i)
  obtain ⟨P,hP,hgood⟩ := private_detector_frame_open (K := K) (by omega) hcap v hv hpair
  refine ⟨e,w,P,hP,?_⟩
  intro frame hframe
  let D := Submodule.span K (Set.range frame)
  let coord := (Module.finBasis K (Forms K h 2 ⧸ D)).equivFun
  let L := coord.toLinearMap.comp D.mkQ
  have hg := hgood frame hframe
  refine ⟨L,?_,?_⟩
  · ext x
    change coord (D.mkQ x)=0 ↔ x∈D
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero D
  · have hA : ∀ i,Function.Injective ((L.comp (mulForm (e (w i)))).comp e.toLinearMap) := by
      intro i
      have hi := coord.injective.comp ((hg.1 i).comp e.injective)
      simpa only [D,L,w,LinearEquiv.apply_symm_apply,LinearMap.coe_comp,LinearEquiv.coe_coe,Function.comp_def] using hi
    apply privatePolynomialMap_kernel_eq_koszul hs ι _ hA w dual hdual
    · intro i j
      change L (mulForm (e (w i)) (e (w j)))=L (mulForm (e (w j)) (e (w i)))
      congr 1
      exact Subtype.ext (mul_comm _ _)
    · intro p x y hxy
      have heq : D.mkQ (mulForm (v p.val.1) (e x))+
          D.mkQ (mulForm (v p.val.2) (e y))=0 := by
        apply coord.injective
        simpa only [map_add,map_zero,L,w,LinearMap.comp_apply,LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using hxy
      obtain ⟨t,hx,hy⟩ := hg.2 p (e x) (e y) heq
      refine ⟨t,?_,?_⟩
      · apply e.injective
        simpa only [map_smul,w,LinearEquiv.apply_symm_apply] using hx
      · apply e.injective
        simpa only [map_smul,w,LinearEquiv.apply_symm_apply] using hy

end Froberg.PrivateColumns
