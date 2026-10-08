import Froberg.GeneratorActions
import Froberg.PolynomialSectionActions
import Froberg.GenericFractionRank

/-! # Actual special-linear actions on coefficient tuples and forms -/

noncomputable section
namespace Froberg
open Matrix Module

variable {K : Type*} [Field K] {n d r : ℕ}

def slFormsAction (d : ℕ) : SpecialLinearGroup (Fin n) K →*
    (Forms K n d ≃ₗ[K] Forms K n d) where
  toFun g := slFormsEquiv g d
  map_one' := by
    apply LinearEquiv.ext
    intro p
    apply Subtype.ext
    exact AlgHom.congr_fun linearSubstitution_one p.val
  map_mul' g h := by
    apply LinearEquiv.ext
    intro p
    apply Subtype.ext
    exact AlgHom.congr_fun (linearSubstitution_mul
      (g : Matrix (Fin n) (Fin n) K) (h : Matrix (Fin n) (Fin n) K)) p.val

def slFormsRepresentation (d : ℕ) :
    Representation K (SpecialLinearGroup (Fin n) K) (Forms K n d) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (slFormsAction d)

abbrev CoefficientGroup (K : Type*) [Field K] (n r : ℕ) :=
  SpecialLinearGroup (Fin n) K × SpecialLinearGroup (Fin r) K

def generatorStandardRepresentation : Representation K (CoefficientGroup K n r) (Fin r → K) :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    SpecialLinearGroup.toLin').comp (MonoidHom.snd _ _)

/-- Coefficient tuples are genuinely linear maps from the generator space. -/
def coefficientLinearMapEquiv : (CoefficientIndex n d r → K) ≃ₗ[K]
    ((Fin r → K) →ₗ[K] Forms K n d) :=
  coefficientCoordinates.symm.trans ((Pi.basisFun K (Fin r)).constr K)

/-- The action on the affine coefficient space is `q ↦ Sym^d(g) q a⁻¹`. -/
def coefficientPointRepresentation :
    Representation K (CoefficientGroup K n r) (CoefficientIndex n d r → K) :=
  coefficientLinearMapEquiv.symm.conjRingEquiv.toMonoidHom.comp
    (Representation.linHom generatorStandardRepresentation
      ((slFormsRepresentation d).comp (MonoidHom.fst _ _)))

/-- The coordinate formula has exactly the inverse-transpose change of
the ordered generating family. -/
theorem coefficientPointRepresentation_forms (g : CoefficientGroup K n r)
    (a : CoefficientIndex n d r → K) :
    coefficientForms K n d r (coefficientPointRepresentation g a) =
      mixFamily ((g.2⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).transpose
        (fun i => slFormsEquiv g.1 d (coefficientForms K n d r a i)) := by
  funext i
  change coefficientCoordinates.symm (coefficientCoordinates
    (((Pi.basisFun K (Fin r)).constr K).symm
      ((slFormsEquiv g.1 d).toLinearMap ∘ₗ
        ((Pi.basisFun K (Fin r)).constr K (coefficientForms K n d r a)) ∘ₗ
        Matrix.toLin' (g.2⁻¹ : SpecialLinearGroup (Fin r) K)))) i = _
  rw [LinearEquiv.symm_apply_apply]
  simp [Basis.constr_symm_apply, Basis.constr_apply_fintype, Matrix.toLin'_apply,
    Matrix.mulVec_single, Pi.basisFun_apply, Pi.basisFun_equivFun, mixFamily,
    map_sum, map_smul]

theorem map_mixFamily {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (L : V →ₗ[K] W)
    (A : Matrix (Fin r) (Fin r) K) (v : Fin r → V) :
    (fun i => L (mixFamily A v i)) = mixFamily A (fun i => L (v i)) := by
  funext i
  simp [mixFamily, map_sum, map_smul]

/-- The source of endpoint multiplication transforms by `a Sym^d(g)`. -/
def coefficientSourceRepresentation :
    Representation K (CoefficientGroup K n r) (Fin r → Forms K n d) where
  toFun g := (mixFamilyLinear (g.2 : Matrix (Fin r) (Fin r) K)).comp
    (LinearMap.pi (fun i => (slFormsRepresentation d g.1).comp (LinearMap.proj i)))
  map_one' := by
    apply LinearMap.ext
    intro f
    change mixFamily (1 : Matrix (Fin r) (Fin r) K)
      (fun i => slFormsRepresentation d 1 (f i)) = f
    simp only [map_one, Module.End.one_apply, mixFamily_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    change mixFamily ((g.2 : Matrix (Fin r) (Fin r) K) * (h.2 : Matrix (Fin r) (Fin r) K))
      (fun i => slFormsRepresentation d (g.1 * h.1) (f i)) =
        mixFamily (g.2 : Matrix (Fin r) (Fin r) K)
          (fun i => slFormsRepresentation d g.1
            (mixFamily (h.2 : Matrix (Fin r) (Fin r) K)
              (fun j => slFormsRepresentation d h.1 (f j)) i))
    rw [map_mixFamily, ← mixFamily_mul]
    simp only [map_mul, Module.End.mul_apply]

/-- Covariance of the actual endpoint multiplication map. -/
theorem coefficient_endpoint_covariance (g : CoefficientGroup K n r)
    (a : CoefficientIndex n d r → K) (f : Fin r → Forms K n d) :
    endpointMultiplication (coefficientForms K n d r (coefficientPointRepresentation g a))
      (coefficientSourceRepresentation g f) =
        slFormsEquiv g.1 (2 * d)
          (endpointMultiplication (coefficientForms K n d r a) f) := by
  rw [coefficientPointRepresentation_forms]
  change endpointMultiplication _
    (mixFamily (g.2 : Matrix (Fin r) (Fin r) K) (fun i => slFormsEquiv g.1 d (f i))) = _
  rw [endpointMultiplication_change_generators _ _
    (show ((g.2⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) * g.2 = 1 by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one])]
  exact (slFormsEquiv_endpointMultiplication g.1 _ _).symm

end Froberg
