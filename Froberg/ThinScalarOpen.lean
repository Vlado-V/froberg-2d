module

public import Froberg.ActualThinSlices
public import Froberg.AffinePolynomialSubstitution

@[expose] public section

/-! The same actual scalar open has full source rank and all thin slices. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic PolynomialBilinearCoordinates
open QuotientCovectorKernel
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q j : ℕ}

theorem principal_open_thin_injective (mu : F →ₗ[K] V →ₗ[K] W)
    (ha : 0 < finrank K V) (hT : finrank K W=q*finrank K V+j)
    (G C : ℝ) (hC : 0 ≤ C) (hG₁ : (finrank K V : ℝ)+C ≤ G)
    (hG₂ : (finrank K V : ℝ)+(j : ℝ)/finrank K V ≤ G)
    (hgrowth : ∀ U : Submodule K V,
      ((finrank K W : ℝ)/finrank K V)*finrank K U+
        G*(min (finrank K U) (finrank K V-finrank K U) : ℕ) ≤
        finrank K (BilinearImage.image mu U)) :
    ∃ P : MvPolynomial (Fin q × Fin (finrank K F)) K,
      ∃ Z : (r : Fin (finrank K V+1)) → Fin (BilinearCovectorStrata.thinSlices j C r.val) → W,
      (∃ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0) ∧
      ∀ Q : Fin q → F,eval (fun ik => coordinates K F (Q ik.1) ik.2) P ≠ 0 →
        Function.Injective (multiplication mu Q) ∧
        ∀ r : Fin (finrank K V+1),∀ ell : W →ₗ[K] K,
          r.val ≤ finrank K (LinearMap.ker (relation mu ell)) →
          (∀ i v,ell (mu (Q i) v)=0) → (∀ t,ell (Z r t)=0) → ell=0 := by
  classical
  obtain ⟨P,Z,hP,hgood⟩ := principal_open_actual_thin_slices mu ha hT G C hC hG₁ hG₂ hgrowth
  have hqa : (q : ℝ) ≤ (finrank K W : ℝ)/finrank K V := by
    apply (le_div_iff₀ (by exact_mod_cast ha)).mpr
    exact_mod_cast (show q*finrank K V ≤ finrank K W by omega)
  obtain ⟨D,hD,hind⟩ := generic_injective_of_strict_shadow mu _ G hqa (by linarith) hgrowth
  let dec : ((Fin q × Fin (finrank K F)) → K) →ₗ[K] (Fin q → F) :=
    LinearMap.pi (fun i => (coordinates K F).symm.toLinearMap.comp
      (LinearMap.pi (fun k => LinearMap.proj (i,k))))
  let L := (coordinates K (Fin q → F)).toLinearMap.comp dec
  let D' := MiddleCoordinates.substituteLinear L D
  have hdec (Q : Fin q → F) : dec (fun ik => coordinates K F (Q ik.1) ik.2)=Q := by
    funext i
    exact (coordinates K F).symm_apply_apply (Q i)
  have hev (Q : Fin q → F) :
      eval (fun ik => coordinates K F (Q ik.1) ik.2) D'=eval (coordinates K _ Q) D := by
    dsimp only [D']
    rw [MiddleCoordinates.eval_substituteLinear]
    change eval (coordinates K _ (dec _)) D=_
    rw [hdec]
  have hDn : D' ≠ 0 := by
    obtain ⟨Q,hQ⟩ := hD
    intro hz
    rw [← hev Q,hz,map_zero] at hQ
    exact hQ rfl
  have hPn : P ≠ 0 := by
    obtain ⟨Q,hQ⟩ := hP
    intro hz
    rw [hz,map_zero] at hQ
    exact hQ rfl
  obtain ⟨x,hx⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hPn hDn)
  refine ⟨P*D',Z,⟨dec x,?_⟩,?_⟩
  · have henc : (fun ik => coordinates K F (dec x ik.1) ik.2)=x := by
      funext ik
      exact congrFun ((coordinates K F).apply_symm_apply (fun k => x (ik.1,k))) ik.2
    rwa [henc]
  · intro Q hQ
    rw [map_mul] at hQ
    have hp := (mul_ne_zero_iff.mp hQ).1
    have hd := (mul_ne_zero_iff.mp hQ).2
    rw [hev] at hd
    exact ⟨hind Q hd,hgood Q hp⟩

end Froberg.BilinearScalarFamily
