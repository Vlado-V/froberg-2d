module

public import Froberg.PolynomialLinearAvoidance

@[expose] public section

/-! Affine shifts do not change the independent-equation budget. In
particular, a common scalar family can be varied with all its fixed positive
components retained in the same equations. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K I V W : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Homogenization uses one shared scalar for every affine equation. -/
def affineHomogenization (A : V →ₗ[K] W) (b : W) : V × K →ₗ[K] W :=
  (A.comp (LinearMap.fst K V K)) + (LinearMap.smulRight (LinearMap.snd K V K) b)

@[simp] lemma affineHomogenization_apply (A : V →ₗ[K] W) (b : W) (x : V × K) :
    affineHomogenization A b x=A x.1+x.2 • b := rfl

lemma affineHomogenization_rank (A : V →ₗ[K] W) (b : W) :
    finrank K A.range ≤ finrank K (affineHomogenization A b).range := by
  apply Submodule.finrank_mono
  rintro _ ⟨v,rfl⟩
  exact ⟨(v,0),by simp⟩

lemma affineHomogenization_polynomial (A : (I → K) → V →ₗ[K] W) (b : (I → K) → W)
    (hA : IsPolynomialFamily A) (hb : IsPolynomialFamily b) :
    IsPolynomialFamily (fun t => affineHomogenization (A t) (b t)) := by
  apply isPolynomialFamily_linearMap
  intro x
  exact (hA.linear_comp (LinearMap.applyₗ (R := K) (M₂ := W) x.1)).add
    ((isPolynomialFamily_const x.2).smul hb)

/-- If the number of parameter coordinates is below the linear equation
rank, one actual scalar choice avoids all the affine equations at once. -/
theorem exists_affine_polynomial_avoidance (A : (I → K) → V →ₗ[K] W)
    (b : (I → K) → W) (hA : IsPolynomialFamily A) (hb : IsPolynomialFamily b)
    {r : ℕ} (hr : Fintype.card I < r) :
    ∃ v : V, ∀ t, r ≤ finrank K (A t).range → A t v+b t ≠ 0 := by
  classical
  let e := (Module.finBasis K (V × K)).equivFun
  obtain ⟨D,⟨xD,hD⟩,havoid⟩ := polynomial_linear_kernel_avoidance
    (fun t => affineHomogenization (A t) (b t)) (affineHomogenization_polynomial A b hA hb) hr
  let C : MvPolynomial (Fin (finrank K (V × K))) K :=
    polynomialOfLinear ((LinearMap.snd K V K).comp e.symm.toLinearMap)
  have hC : eval (e (0,1)) C=1 := by
    rw [eval_polynomialOfLinear]
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,LinearMap.snd_apply]
  let P : Fin 2 → MvPolynomial (Fin (finrank K (V × K))) K := ![D,C]
  have hP (i : Fin 2) : P i ≠ 0 := by
    fin_cases i
    · intro h
      have hz : D=0 := h
      exact hD (by rw [hz,map_zero])
    · intro h
      have hz : C=0 := by simpa [P] using h
      simp [hz] at hC
  obtain ⟨x,hx⟩ := nonempty_principal_intersection P hP
  let z : V × K := e.symm x
  have hz : z.2 ≠ 0 := by
    have hh := hx 1
    change eval x C ≠ 0 at hh
    rwa [eval_polynomialOfLinear] at hh
  refine ⟨z.2⁻¹ • z.1,?_⟩
  intro t ht he
  have hd : eval x D ≠ 0 := hx 0
  apply havoid x hd t (ht.trans (affineHomogenization_rank (A t) (b t)))
  change A t z.1+z.2 • b t=0
  have hh := congrArg (fun w : W => z.2 • w) he
  simpa only [smul_add,map_smul,smul_smul,mul_inv_cancel₀ hz,one_smul,smul_zero] using hh

end Froberg
