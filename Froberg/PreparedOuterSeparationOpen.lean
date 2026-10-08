import Froberg.PreparedQuadraticSeparationOpen
import Froberg.PreparedQuadraticFormalSeparation
import Froberg.PreparedLowComponentInstances
import Froberg.PreparedOuterSeparation

/-! The actual low components identify the polynomial quadratic row
certificate with C.2 on the full prepared parameter space. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters FullPreparedParameters
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f u c : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem preparedScalarSpace_eq_familySpace
    (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (p : PreparedParameters.Space m d q J counts O) :
    preparedScalarSpace p=familySpace (fun i => p.1 (idx i)) := by
  apply congrArg (Submodule.span K)
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨idx.symm i,congrArg (fun j => (p.1 j).val) (idx.apply_symm_apply i)⟩
  · rintro ⟨i,rfl⟩
    exact ⟨idx i,rfl⟩

theorem prepared_outer_separation_of_quadratic_row
    (hd : 3≤d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hmin : ∀ j∈J,2≤j) (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (T : Poly K h →ₗ[K] (Fin c → K)) (hT : T.comp (homogeneousComponent 2)=T)
    (hO₂ : O 2≤T.ker) (U : Fin u → Forms K h d)
    (p : FixedPureZeroScalarSpace m d q f u J counts O)
    (hrow : PreparedQuadraticRowSeparated (t := d-2) idx (biformVectorDetector T) p) :
    PreparedOuterSeparation (by omega) ho hO hJ heven U p := by
  intro D hD
  have hlow := prepared_private_background_lowComponents hd ho hO hJ heven hmin U p.1 p.2.2 p.2.1
  rw [preparedScalarSpace_eq_familySpace idx] at hlow
  apply prepared_quadratic_formal_separation (by omega) T hT
    (fun i => p.2.1.1 (idx i)) p.1 p.2.2
    (fun i => oddPolynomialToForms (preparedOddBiform (by omega) ho U p.1 p.2.2 (Sum.inl i)))
    _ (O 2) hO₂ _ hlow hrow D hD
  intro i
  change rename finSumFinEquiv ((p.2.2 i).val+0)=rename finSumFinEquiv (p.2.2 i).val
  rw [add_zero]

theorem prepared_outer_separation_principal_open
    (hd : 3≤d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hmin : ∀ j∈J,2≤j) (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (T : Poly K h →ₗ[K] (Fin c → K)) (hT : T.comp (homogeneousComponent 2)=T)
    (hO₂ : O 2≤T.ker) (U : Fin u → Forms K h d)
    (Q₀ : Fin r → Forms K m d) (P₀ : OuterSpace K (Fin h) m d u)
    (F₀ : OuterSpace K (Fin h) m d f)
    (hexact : (quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
      (biformVectorDetector T) Q₀ P₀).ker=(quadraticNuisanceBoundary P₀).range)
    (hsep : ∀ x z,quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
      (biformVectorDetector T) Q₀ P₀ x+
      detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) F₀ z=0 → z=0) :
    letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
      finite_fixedPureZeroScalarSpace hO
    ∃ D : MvPolynomial (Fin (finrank K (FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          PreparedOuterSeparation (by omega) ho hO hJ heven U p := by
  letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
    finite_fixedPureZeroScalarSpace hO
  obtain ⟨D,hD,hgood⟩ := prepared_quadratic_separation_principal_open hO idx
    (biformVectorDetector T) Q₀ P₀ F₀ hexact hsep
  exact ⟨D,hD,fun p hp => prepared_outer_separation_of_quadratic_row
    hd ho hO hJ heven hmin idx T hT hO₂ U p (hgood p hp)⟩

theorem prepared_outer_separation_principal_open_uniform
    (hd : 3≤d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hmin : ∀ j∈J,2≤j) (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (T : Poly K h →ₗ[K] (Fin c → K)) (hT : T.comp (homogeneousComponent 2)=T)
    (hO₂ : O 2≤T.ker)
    (Q₀ : Fin r → Forms K m d) (P₀ : OuterSpace K (Fin h) m d u)
    (F₀ : OuterSpace K (Fin h) m d f)
    (hexact : (quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
      (biformVectorDetector T) Q₀ P₀).ker=(quadraticNuisanceBoundary P₀).range)
    (hsep : ∀ x z,quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
      (biformVectorDetector T) Q₀ P₀ x+
      detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) F₀ z=0 → z=0) :
    letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
      finite_fixedPureZeroScalarSpace hO
    ∃ D : MvPolynomial (Fin (finrank K (FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ (U : Fin u → Forms K h d) (p : FixedPureZeroScalarSpace m d q f u J counts O),
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          PreparedOuterSeparation (by omega) ho hO hJ heven U p := by
  letI : Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts O) :=
    finite_fixedPureZeroScalarSpace hO
  obtain ⟨D,hD,hgood⟩ := prepared_quadratic_separation_principal_open hO idx
    (biformVectorDetector T) Q₀ P₀ F₀ hexact hsep
  exact ⟨D,hD,fun U p hp => prepared_outer_separation_of_quadratic_row
    hd ho hO hJ heven hmin idx T hT hO₂ U p (hgood p hp)⟩

end Froberg.PreparedTarget
