module

public import Froberg.RestoredQuadraticParameters
public import Froberg.DetectedBiformSeparation

@[expose] public section

/-! The scalar and detected outer-product row is injective on a genuine
open of the complete restored parameter space. Every scalar tail is used. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {h m d r f c t : ℕ}

namespace PreparedParameters
variable {q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

def QuadraticSeparated (T : Poly K h →ₗ[K] (Fin c → K))
    (p : QuadraticParameters K h m d r f) : Prop :=
  ∀ (x : Fin r → Fin c → Forms K m (d-2)) (z : Sym2 (Fin f) → K),
    scalarCoefficientRow p.1 x+
      detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) p.2 z=0 → z=0

theorem quadratic_separated_principal_open
    (T : Poly K h →ₗ[K] (Fin c → K))
    (Q₀ : Fin r → Forms K m d) (F₀ : Fin f → FullBiform K (Fin h) m 1 (d-1))
    (hQ₀ : Function.Injective (prefixMultiplication Q₀ (d-2)))
    (hsep : QuadraticSeparated T (Q₀,F₀)) :
    ∃ D : MvPolynomial (Fin (finrank K (QuadraticParameters K h m d r f))) K,
      eval ((Module.finBasis K _).equivFun (Q₀,F₀)) D≠0 ∧
      ∀ p : QuadraticParameters K h m d r f,
        eval ((Module.finBasis K _).equivFun p) D≠0 → QuadraticSeparated T p := by
  classical
  let coord := (Module.finBasis K (QuadraticParameters K h m d r f)).equivFun
  let S := Fin r → Fin c → Forms K m (d-2)
  let Z := Sym2 (Fin f) → K
  let j := (FullBiform K (Fin h) m 1 (d-1)).subtype
  let A : (Fin (finrank K (QuadraticParameters K h m d r f)) → K) →
      (S × Z) →ₗ[K] (Fin c → Poly K m) := fun a =>
    addRow (scalarCoefficientRow (coord.symm a).1)
      (detectedSymmetricProductRow j (biformVectorDetector T) (coord.symm a).2)
  let Q : (Fin (finrank K (QuadraticParameters K h m d r f)) → K) →ₗ[K]
      (Fin r → Forms K m d) := (LinearMap.fst K _ _).comp coord.symm.toLinearMap
  let F : (Fin (finrank K (QuadraticParameters K h m d r f)) → K) →ₗ[K]
      (Fin f → FullBiform K (Fin h) m 1 (d-1)) :=
    (LinearMap.snd K _ _).comp coord.symm.toLinearMap
  have hpoly : IsPolynomialFamily A := by
    apply isPolynomialFamily_linearMap
    intro x
    exact ((isPolynomialFamily_linear Q).linear_comp (scalarCoefficientRowInFamily x.1)).add
      ((detectedSymmetricProductRow_polynomial j (biformVectorDetector T) F
        (isPolynomialFamily_linear F)).linear_comp (LinearMap.applyₗ (R := K) x.2))
  have hi : Function.Injective (A (coord (Q₀,F₀))) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have he : scalarCoefficientRow Q₀ x.1+
        detectedSymmetricProductRow j (biformVectorDetector T) F₀ x.2=0 := by
      simpa only [A,addRow_apply,LinearEquiv.symm_apply_apply] using hx
    have hz := hsep x.1 x.2 he
    have hx0 : x.1=0 := scalarCoefficientRow_injective Q₀ hQ₀ (by simpa only [hz,map_zero,add_zero] using he)
    exact Prod.ext hx0 hz
  obtain ⟨D,hD,hgood⟩ := rank_polynomial_general_open A hpoly (coord (Q₀,F₀))
  refine ⟨D,hD,?_⟩
  intro p hp x z hxz
  have hrank := hgood (coord p) hp
  rw [LinearMap.finrank_range_of_inj hi] at hrank
  have hdim := (A (coord p)).finrank_range_add_finrank_ker
  have hinj : Function.Injective (A (coord p)) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    omega
  have hzero : A (coord p) (x,z)=A (coord p) 0 := by
    simpa only [A,addRow_apply,LinearEquiv.symm_apply_apply,map_zero] using hxz
  exact congrArg Prod.snd (hinj hzero)

theorem restored_quadratic_separation_open
    (hO : ∀ j∈J,O j≤Forms K h j) (idx : Fin r ≃ Label q J counts)
    (T : Poly K h →ₗ[K] (Fin c → K))
    (Q₀ : Fin r → Forms K m d) (F₀ : Fin f → FullBiform K (Fin h) m 1 (d-1))
    (hQ₀ : Function.Injective (prefixMultiplication Q₀ (d-2)))
    (hsep : QuadraticSeparated T (Q₀,F₀)) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          QuadraticSeparated T (restoredC2Projection idx p) := by
  obtain ⟨D,hD,hgood⟩ := quadratic_separated_principal_open T Q₀ F₀ hQ₀ hsep
  exact restored_c2_principal_pullback hO idx D ⟨(Q₀,F₀),hD⟩ (QuadraticSeparated T) hgood


/-- Actual paired scalar and output spaces supply the separation witness;
all remaining restored coefficients are free parameters of the open. -/
theorem restored_quadratic_separation_open_of_scalar_space
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hO : ∀ j∈J,O j≤Forms K h j) (idx : Fin r ≃ Label q J counts)
    (T : Poly K h →ₗ[K] (Fin c → K))
    (Q₀ : Fin r → Forms K m d)
    (hQ₀ : Function.Injective (prefixMultiplication Q₀ (d-2)))
    (o : ι → Forms K h 1)
    (ho : LinearIndependent K (fun a => T (pairProducts (fun i => (o i).val) a)))
    (C : Submodule K (Poly K m)) (hCdeg : C≤Forms K m (d-1))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCQ : Disjoint (C*C) (familySpace Q₀*Forms K m (d-2)))
    (hf : f≤Fintype.card ι*(finrank K C/2)) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          QuadraticSeparated T (restoredC2Projection idx p) := by
  obtain ⟨F,hF,hsep⟩ := exists_scalar_separated_biform_family Q₀ o T ho C hCdeg hC hCQ hf
  exact restored_quadratic_separation_open hO idx T Q₀ F hQ₀ hsep

end PreparedParameters
end Froberg
