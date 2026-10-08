import Froberg.GeneralLinearColumns
import Froberg.PrivateKoszulKernel

/-! The private-power kernel theorem applied to an actually constructed
quadratic detector, in finite coefficient coordinates. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PrivateColumns
open Module
variable {K : Type*} [Field K] [Infinite K] {a z s b h c : ℕ}

/-- All private-output hypotheses are realized by actual linear-form
products followed by one common quadratic detector. -/
theorem exists_private_detector_model (hh : 2≤h) (hc : 2*h-1≤c) :
    ∃ (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
      (w : Fin b → Fin h → K) (L : Forms K h 2 →ₗ[K] (Fin c → K))
      (dual : Fin b → (Fin h → K) →ₗ[K] K),
      (∀ i, dual i (w i)=1) ∧
      (∀ i, Function.Injective ((L.comp (mulForm (e (w i)))).comp e.toLinearMap)) ∧
      (∀ i j, L (mulForm (e (w i)) (e (w j)))=L (mulForm (e (w j)) (e (w i)))) ∧
      (∀ p : GeneratorPair b, ∀ x y,
        L (mulForm (e (w p.val.1)) (e x))+L (mulForm (e (w p.val.2)) (e y))=0 →
        ∃ t : K, x=t • w p.val.2 ∧ y=(-t) • w p.val.1) := by
  let e : (Fin h → K) ≃ₗ[K] Forms K h 1 := LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_forms K h 1 (by omega)]
    simp)
  obtain ⟨v,L,hv,hL,hpair⟩ := exists_general_detected_private_outputs (K := K) hh hc b
  let w : Fin b → Fin h → K := fun i => e.symm (v i)
  have hw (i : Fin b) : w i ≠ 0 := by
    intro hz
    apply hv i
    have hh := congrArg e hz
    simpa only [w,LinearEquiv.apply_symm_apply,map_zero] using hh
  choose dual hdual using fun i => Module.Projective.exists_dual_eq_one K (hw i)
  refine ⟨e,w,L,dual,hdual,?_,?_,?_⟩
  · intro i
    simpa only [w,LinearEquiv.apply_symm_apply,LinearMap.coe_comp,LinearEquiv.coe_coe] using (hL i).comp e.injective
  · intro i j
    congr 1
    exact Subtype.ext (mul_comm _ _)
  · intro p x y hxy
    have hxy' : L (mulForm (v p.val.1) (e x))+L (mulForm (v p.val.2) (e y))=0 := by
      simpa only [w,LinearEquiv.apply_symm_apply] using hxy
    obtain ⟨t,ht,ht'⟩ := hpair p (e x) (e y) hxy'
    refine ⟨t,?_,?_⟩
    · apply e.injective
      simpa only [map_smul,w,LinearEquiv.apply_symm_apply] using ht
    · apply e.injective
      simpa only [map_smul,w,LinearEquiv.apply_symm_apply] using ht'

/-- The full private-row endpoint exactness is attained by a genuine
common quadratic detector over any infinite field. -/
theorem exists_private_row_exact (hh : 2≤h) (hc : 2*h-1≤c) (hs : 0<s)
    (ι : Fin b ↪ Fin z) :
    ∃ (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
      (w : Fin b → Fin h → K) (L : Forms K h 2 →ₗ[K] (Fin c → K)),
      let A := fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap
      (privatePolynomialMap (a := a) (s := s) ι A).ker =
        Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))) := by
  obtain ⟨e,w,L,dual,hdual,hA,hcomm,hpair⟩ := exists_private_detector_model (K := K) (b := b) hh hc
  refine ⟨e,w,L,?_⟩
  apply privatePolynomialMap_kernel_eq_koszul hs ι _ hA w dual hdual
  · exact hcomm
  · exact hpair

end Froberg.PrivateColumns
