import Froberg.PreparedOddParameterProjection
import Froberg.GenericDimensions

/-! Independent scalar and vector leading families form a nonempty
principal open whenever both elementary dimension bounds hold. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K]

theorem finite_family_independence_open {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] {r : ℕ} (hr : r≤finrank K V) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin r → V))) K,
      (∃ v : Fin r → V,eval ((Module.finBasis K _).equivFun v) P≠0) ∧
      ∀ v : Fin r → V,eval ((Module.finBasis K _).equivFun v) P≠0 → LinearIndependent K v := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank hr
  let b := (Module.finBasis K (Fin r → V)).equivFun
  let family := fun i : Fin r => (LinearMap.proj i).comp b.symm.toLinearMap
  obtain ⟨P,hP,hgood⟩ := independent_principal_open family (b v)
    (by simpa only [family,LinearMap.comp_apply,LinearMap.proj_apply,
      LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hv)
  refine ⟨P,⟨v,hP⟩,?_⟩
  intro w hw
  simpa only [family,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hgood (b w) hw

theorem scalar_vector_independence_open {h m d f q : ℕ}
    (hq : q≤finrank K (Forms K m d)) (hf : f≤finrank K (Rows K h m (d-1))) :
    ∃ P : MvPolynomial (Fin (finrank K (ScalarVectorParameters K h m d f q))) K,
      (∃ p : ScalarVectorParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
      ∀ p : ScalarVectorParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) P≠0 →
        LinearIndependent K p.1 ∧ LinearIndependent K p.2 := by
  obtain ⟨D,hD,hgoodD⟩ := finite_family_independence_open (K := K) hf
  obtain ⟨E,hE,hgoodE⟩ := finite_family_independence_open (K := K) hq
  obtain ⟨D',hD',hgD⟩ := principal_open_linear_pullback
    (LinearMap.fst K (Fin f → Rows K h m (d-1)) (Fin q → Forms K m d))
    (fun v => ⟨(v,0),rfl⟩) D hD _ hgoodD
  obtain ⟨E',hE',hgE⟩ := principal_open_linear_pullback
    (LinearMap.snd K (Fin f → Rows K h m (d-1)) (Fin q → Forms K m d))
    (fun v => ⟨(0,v),rfl⟩) E hE _ hgoodE
  obtain ⟨x,hxD,hxE⟩ := principal_opens_intersect
    (by obtain ⟨p,hp⟩ := hD'; exact ⟨(Module.finBasis K _).equivFun p,hp⟩)
    (by obtain ⟨p,hp⟩ := hE'; exact ⟨(Module.finBasis K _).equivFun p,hp⟩)
  refine ⟨D'*E',⟨(Module.finBasis K _).equivFun.symm x,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply,map_mul] using mul_ne_zero hxD hxE
  · intro p hp
    have hh := mul_ne_zero_iff.mp (show eval ((Module.finBasis K _).equivFun p) D'*
      eval ((Module.finBasis K _).equivFun p) E'≠0 by simpa only [map_mul] using hp)
    exact ⟨hgD p hh.1,hgE p hh.2⟩

end Froberg
