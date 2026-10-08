import Froberg.ScalarShadowBudgets

/-! Generic scalar surjectivity transported from coordinates to arbitrary
finite-dimensional polynomial or quotient spaces. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K F V W F' V' W' : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup F'] [Module K F'] [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']

def transportBilinear (eF : F ≃ₗ[K] F') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : F →ₗ[K] V →ₗ[K] W) : F' →ₗ[K] V' →ₗ[K] W' :=
  (conjugate eV eW mu).comp eF.symm.toLinearMap

@[simp] lemma transportBilinear_apply (eF : F ≃ₗ[K] F') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : F →ₗ[K] V →ₗ[K] W) (f : F') (v : V') :
    transportBilinear eF eV eW mu f v = eW (mu (eF.symm f) (eV.symm v)) := rfl

lemma image_transportBilinear (eF : F ≃ₗ[K] F') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : F →ₗ[K] V →ₗ[K] W) (L : Submodule K V') :
    Quartic.BilinearImage.image (transportBilinear eF eV eW mu) L =
      (Quartic.BilinearImage.image mu (L.map eV.symm.toLinearMap)).map eW.toLinearMap := by
  apply le_antisymm
  · apply iSup_le
    intro f
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨_,Quartic.BilinearImage.product_mem mu _ (eF.symm f) (eV.symm v) ⟨v,hv,rfl⟩,rfl⟩
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    intro f
    rintro _ ⟨v,⟨x,hx,rfl⟩,rfl⟩
    change eW (mu f (eV.symm x)) ∈ Quartic.BilinearImage.image (transportBilinear eF eV eW mu) L
    simpa only [transportBilinear_apply,LinearEquiv.symm_apply_apply] using
      Quartic.BilinearImage.product_mem (transportBilinear eF eV eW mu) L (eF f) x hx

lemma surjective_of_transport [FiniteDimensional K F] [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K F'] [FiniteDimensional K V'] [FiniteDimensional K W'] {q : ℕ}
    (eF : F ≃ₗ[K] F') (eV : V ≃ₗ[K] V') (eW : W ≃ₗ[K] W')
    (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F')
    (hQ : Function.Surjective (multiplication (transportBilinear eF eV eW mu) Q)) :
    Function.Surjective (multiplication mu (fun i => eF.symm (Q i))) := by
  intro y
  obtain ⟨x,hx⟩ := hQ (eW y)
  refine ⟨fun i => eV.symm (x i),eW.injective ?_⟩
  rw [multiplication_apply] at hx
  rw [multiplication_apply,map_sum]
  simpa only [transportBilinear_apply] using hx

variable [FiniteDimensional K F] [FiniteDimensional K V] [FiniteDimensional K W]

/-- A nonempty principal open of actual scalar families is surjective when
the number of scalar forms is above the target/source ratio. -/
theorem generic_surjective_actual_of_strict_shadow [Infinite K] {q : ℕ}
    (mu : F →ₗ[K] V →ₗ[K] W) (R D : ℝ)
    (hT : (finrank K W : ℝ)=R*finrank K V) (hq : R ≤ q) (hD : (finrank K V : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K V,
      R*finrank K L+D*(min (finrank K L) (finrank K V-finrank K L) : ℕ) ≤
        finrank K (Quartic.BilinearImage.image mu L)) :
    ∃ P : MvPolynomial (Fin q × Fin (finrank K F)) K,
      (∃ Q : Fin q → F, eval (fun ij => coordinates K F (Q ij.1) ij.2) P ≠ 0) ∧
      ∀ Q : Fin q → F, eval (fun ij => coordinates K F (Q ij.1) ij.2) P ≠ 0 →
        Function.Surjective (multiplication mu Q) := by
  let eF := coordinates K F
  let eV := coordinates K V
  let eW := coordinates K W
  let mu' := transportBilinear eF eV eW mu
  have hG (L : Submodule K (Fin (finrank K V) → K)) :
      R*finrank K L+D*(min (finrank K L) (finrank K V-finrank K L) : ℕ) ≤
        finrank K (Quartic.BilinearImage.image mu' L) := by
    have hh := hgrowth (L.map eV.symm.toLinearMap)
    rw [eV.symm.finrank_map_eq] at hh
    change _ ≤ (finrank K (Quartic.BilinearImage.image (transportBilinear eF eV eW mu) L) : ℝ)
    rw [image_transportBilinear,eW.finrank_map_eq]
    exact hh
  obtain ⟨P,hP,hSurj⟩ := BilinearCovectorStrata.generic_surjective_of_strict_shadow mu' R D hT hq hD hG
  refine ⟨P,?_,?_⟩
  · obtain ⟨Q,hQ⟩ := hP
    refine ⟨fun i => eF.symm (fun j => Q (i,j)),?_⟩
    simpa only [eF,LinearEquiv.apply_symm_apply] using hQ
  · intro Q hQ
    have hs := surjective_of_transport eF eV eW mu
      (fun i => eF (Q i)) (hSurj (fun ij => eF (Q ij.1) ij.2) hQ)
    simpa only [LinearEquiv.symm_apply_apply] using hs

end Froberg.BilinearScalarFamily
