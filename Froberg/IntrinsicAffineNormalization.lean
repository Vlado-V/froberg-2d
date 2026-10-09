module

public import Froberg.PrincipalAffineNormalization

@[expose] public section

/-! Affine normalization without imposing a special basis on the parameter space. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K V : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem intrinsic_principal_open_affine_normalization
    (D : MvPolynomial (Fin (finrank K (V × K))) K)
    (hD : ∃ y,eval y D≠0) (Good : V × K → Prop)
    (hgood : ∀ y,eval y D≠0 → Good ((Module.finBasis K (V × K)).equivFun.symm y))
    (hscale : ∀ c : K,c≠0 → ∀ y,Good (c • y) → Good y) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ x,eval x P≠0) ∧ ∀ x,eval x P≠0 → Good ((Module.finBasis K V).equivFun.symm x,1) := by
  classical
  let e := (Module.finBasis K (V × K)).equivFun
  let f := (Module.finBasis K V).equivFun
  let C : MvPolynomial (Fin (finrank K (V × K))) K :=
    polynomialOfLinear ((LinearMap.snd K V K).comp e.symm.toLinearMap)
  have hC : eval (e (0,1)) C=1 := by
    rw [eval_polynomialOfLinear]
    simp
  let Ds : Fin 2 → MvPolynomial (Fin (finrank K (V × K))) K := ![D,C]
  have hDs (i : Fin 2) : Ds i≠0 := by
    fin_cases i
    · obtain ⟨x,hx⟩ := hD
      intro hz
      have hz' : D=0 := hz
      exact hx (by rw [hz',map_zero])
    · intro hz
      have hz' : C=0 := hz
      rw [hz',map_zero] at hC
      exact zero_ne_one hC
  obtain ⟨x,hx⟩ := nonempty_principal_intersection Ds hDs
  let z := e.symm x
  let c := z.2
  have hc : c≠0 := by
    have hh := hx 1
    change eval x C≠0 at hh
    simpa only [C,eval_polynomialOfLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearMap.snd_apply] using hh
  let F : (Fin (finrank K V) → K) →ₗ[K] (Fin (finrank K (V × K)) → K) :=
    c • (e.toLinearMap.comp ((LinearMap.inl K V K).comp f.symm.toLinearMap))
  let offset := e (0,c)
  have hF (y : Fin (finrank K V) → K) : F y+offset=e (c • (f.symm y,1)) := by
    simp only [F,offset,LinearMap.smul_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearMap.inl_apply,←map_smul,←map_add]
    congr 1
    ext <;> simp
  let y₀ := f (c⁻¹ • z.1)
  have hz : c • (f.symm y₀,1)=z := by
    simp only [y₀,LinearEquiv.symm_apply_apply,Prod.smul_mk,smul_smul,
      mul_inv_cancel₀ hc,one_smul,smul_eq_mul,mul_one]
    rfl
  refine ⟨substituteAffine F offset D,⟨y₀,?_⟩,?_⟩
  · rw [eval_substituteAffine,hF,hz]
    have he : e z=x := e.apply_symm_apply x
    rw [he]
    exact hx 0
  · intro y hy
    rw [eval_substituteAffine,hF] at hy
    have hg := hgood _ hy
    rw [e.symm_apply_apply] at hg
    exact hscale c hc _ hg

end Froberg
