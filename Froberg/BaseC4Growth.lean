import Froberg.OddScalarParameters
import Froberg.AmbientTopGrowth
import Froberg.FiniteBasisPrincipalIntersection

/-! One open in the actual F/Q coefficients supplies the top and every
ordinary odd-row growth condition used by C.4. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f b t : ℕ}

def topScalarParametersEquiv (hd : 1 ≤ d) :
    OddScalarParameters K h m d f q ≃ₗ[K] ProjectedTopParameters K h m (d-1) f q where
  toFun p := topGrowthParameters hd p.2 p.1
  invFun p := (p.1,fun i => topGrowthDegree hd m (p.2 i))
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      exact (topGrowthDegree hd m).apply_symm_apply _
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      exact (topGrowthDegree hd m).symm_apply_apply _
  map_add' p z := by
    apply Prod.ext
    · rfl
    · funext i
      exact (topGrowthDegree hd m).symm.map_add _ _
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · funext i
      exact (topGrowthDegree hd m).symm.map_smul c _

attribute [local irreducible] OddScalarLayerProperty

theorem top_scalar_growth_open (hd : 1 ≤ d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (htop : ProjectedTopGrowthOpen R m f q t) :
    ∃ D : MvPolynomial (Fin (finrank K (OddScalarParameters K h m d f q))) K,
      (∃ p : OddScalarParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : OddScalarParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (projectedTopMap R (topGrowthParameters hd p.2 p.1)) ∧
        ∀ L : Submodule K (Fin b → K),t*finrank K L ≤
          finrank K (BilinearImage.image (projectedTopScalarAction R (topGrowthParameters hd p.2 p.1)) L) := by
  obtain ⟨D,hD,hgood⟩ := htop
  let ec := topScalarParametersEquiv (K := K) (h := h) (m := m) (q := q) (f := f) hd
  let eU := (Module.finBasis K (OddScalarParameters K h m d f q)).equivFun
  let eE := (Module.finBasis K (ProjectedTopParameters K h m (d-1) f q)).equivFun
  let L := eE.toLinearMap.comp (ec.toLinearMap.comp eU.symm.toLinearMap)
  let P := substituteAffine L 0 D
  have heval (p : OddScalarParameters K h m d f q) :
      eval (eU p) P=eval (eE (ec p)) D := by
    rw [show P=substituteAffine L 0 D from rfl,eval_substituteAffine]
    simp only [add_zero,L,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  obtain ⟨z,hz⟩ := hD
  refine ⟨P,⟨ec.symm z,?_⟩,?_⟩
  · change eval (eU (ec.symm z)) P≠0
    rw [heval,ec.apply_symm_apply]
    exact hz
  · intro p hp
    apply hgood (ec p)
    change eval (eU p) P≠0 at hp
    rw [heval] at hp
    exact hp

theorem base_c4_growth_open (hd : 1 ≤ d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (htop : ProjectedTopGrowthOpen R m f q t)
    (hmid : HasOddScalarLayersOpen K h m d f q t) :
    ∃ D : MvPolynomial (Fin (finrank K (OddScalarParameters K h m d f q))) K,
      (∃ p : OddScalarParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : OddScalarParameters K h m d f q,eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (projectedTopMap R (topGrowthParameters hd p.2 p.1)) ∧
        (∀ L : Submodule K (Fin b → K),t*finrank K L ≤
          finrank K (BilinearImage.image (projectedTopScalarAction R (topGrowthParameters hd p.2 p.1)) L)) ∧
        ∀ (k : ℕ) (hk : 3 ≤ k) (hkd : k ≤ d),
          OddScalarLayerProperty t (by omega) hkd (oddScalarBiformParameters p) := by
  obtain ⟨A,hA,hAtop⟩ := top_scalar_growth_open (K := K) (h := h) (m := m) (d := d) (q := q) (f := f) (b := b) (t := t) hd R htop
  obtain ⟨B,hB,hBmid⟩ := odd_scalar_forms_open (K := K) (h := h) (n := m) (d := d) (qO := f) (qS := q) (t := t) hmid
  have hnz : ∀ i : Fin 2,(![A,B] i)≠0 := by
    intro i
    fin_cases i
    · obtain ⟨p,hp⟩ := hA
      intro hz
      exact hp (by rw [show A=0 from hz,map_zero])
    · obtain ⟨p,hp⟩ := hB
      intro hz
      exact hp (by rw [show B=0 from hz,map_zero])
  obtain ⟨x,hx⟩ := Quartic.nonempty_principal_intersection ![A,B] hnz
  refine ⟨A*B,⟨(Module.finBasis K (OddScalarParameters K h m d f q)).equivFun.symm x,?_⟩,?_⟩
  · simp only [LinearEquiv.apply_symm_apply,eval_mul]
    exact mul_ne_zero (hx 0) (hx 1)
  · intro z hz
    rw [eval_mul] at hz
    have ha := hAtop z (mul_ne_zero_iff.mp hz).1
    exact ⟨ha.1,ha.2,hBmid z (mul_ne_zero_iff.mp hz).2⟩

end Froberg
