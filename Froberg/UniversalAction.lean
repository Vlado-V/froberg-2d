module

public import Froberg.CoefficientActions
public import Froberg.InvariantSubspaces
public import Froberg.SemilinearKernel

@[expose] public section

/-! # Covariance of the actual universal multiplication matrix -/

noncomputable section
namespace Froberg
open Matrix Module MvPolynomial

variable {K : Type*} [Field K] [Infinite K] {n d r : ℕ}

def endpointTargetRepresentation :
    Representation K (CoefficientGroup K n r) (Forms K n (2 * d)) :=
  (slFormsRepresentation (2 * d)).comp (MonoidHom.fst _ _)

def endpointTargetCoordinates :
    Representation K (CoefficientGroup K n r)
      (Fin (finrank K (Forms K n (2 * d))) → K) :=
  coordinateRepresentation (Module.finBasis K (Forms K n (2 * d))) endpointTargetRepresentation

def endpointSourceCoordinates :
    Representation K (CoefficientGroup K n r)
      (Fin (finrank K (Fin r → Forms K n d)) → K) :=
  coordinateRepresentation (Module.finBasis K (Fin r → Forms K n d)) coefficientSourceRepresentation

def universalTargetAction : SemilinearMatrixAction K (MvPolynomial (CoefficientIndex n d r) K)
    (CoefficientGroup K n r) (Fin (finrank K (Forms K n (2 * d)))) :=
  polynomialSectionAction coefficientPointRepresentation endpointTargetCoordinates

/-- The universal matrix satisfies the covariance identity over its
polynomial coefficient ring, proved by evaluating the actual maps. -/
theorem universalMultiplicationMatrix_covariance (g : CoefficientGroup K n r) :
    universalMultiplicationMatrix K n d r *
        (LinearMap.toMatrix' (endpointSourceCoordinates (d := d) g)).map C =
      (universalTargetAction (d := d)).matrix g *
        (universalMultiplicationMatrix K n d r).map ((universalTargetAction (d := d)).coeff g) := by
  apply polynomial_matrix_covariance_of_evaluation coefficientPointRepresentation g
  intro a
  let b := coefficientPointRepresentation g⁻¹ a
  have hp : coefficientPointRepresentation g b = a :=
    Representation.self_inv_apply coefficientPointRepresentation g a
  have hc : (endpointMultiplication (coefficientForms K n d r a)).comp
      (coefficientSourceRepresentation g) =
      (endpointTargetRepresentation g).comp
        (endpointMultiplication (coefficientForms K n d r b)) := by
    apply LinearMap.ext
    intro f
    have hh := coefficient_endpoint_covariance g b f
    rw [hp] at hh
    exact hh
  have hm := congrArg (LinearMap.toMatrix (Module.finBasis K (Fin r → Forms K n d))
    (Module.finBasis K (Forms K n (2 * d)))) hc
  rw [LinearMap.toMatrix_comp (Module.finBasis K (Fin r → Forms K n d))
    (Module.finBasis K (Fin r → Forms K n d)) (Module.finBasis K (Forms K n (2 * d))),
    LinearMap.toMatrix_comp (Module.finBasis K (Fin r → Forms K n d))
      (Module.finBasis K (Forms K n (2 * d))) (Module.finBasis K (Forms K n (2 * d)))] at hm
  simpa only [universalMultiplicationMatrix_eval, endpointSourceCoordinates,
    endpointTargetCoordinates, coordinateRepresentation_toMatrix] using hm

variable {F : Type*} [Field F]
  [Algebra (MvPolynomial (CoefficientIndex n d r) K) F]
  [IsFractionRing (MvPolynomial (CoefficientIndex n d r) K) F]

/-- The actual image of universal multiplication over the fraction field
is stable under the constructed semilinear target action. -/
theorem universalMultiplication_image_invariant (g : CoefficientGroup K n r)
    (w : Fin (finrank K (Forms K n (2 * d))) → F)
    (hw : w ∈ LinearMap.range
      ((universalMultiplicationMatrix K n d r).map
        (algebraMap (MvPolynomial (CoefficientIndex n d r) K) F)).mulVecLin) :
    ((universalTargetAction (d := d)).matrix g).map
        (algebraMap (MvPolynomial (CoefficientIndex n d r) K) F) *ᵥ
      (fun i => IsFractionRing.ringEquivOfRingEquiv
        ((universalTargetAction (d := d)).coeff g).toRingEquiv (w i)) ∈
      LinearMap.range ((universalMultiplicationMatrix K n d r).map
        (algebraMap (MvPolynomial (CoefficientIndex n d r) K) F)).mulVecLin := by
  let φ := algebraMap (MvPolynomial (CoefficientIndex n d r) K) F
  let E : F ≃+* F := IsFractionRing.ringEquivOfRingEquiv
    ((universalTargetAction (d := d)).coeff g).toRingEquiv
  let A := (LinearMap.toMatrix' (endpointSourceCoordinates (d := d) g)).map
    (C : K →+* MvPolynomial (CoefficientIndex n d r) K)
  have hc := congrArg (fun M => M.map φ) (universalMultiplicationMatrix_covariance (d := d) g)
  simp only [Matrix.map_mul] at hc
  have he : ((universalMultiplicationMatrix K n d r).map ((universalTargetAction (d := d)).coeff g)).map φ =
      ((universalMultiplicationMatrix K n d r).map φ).map E := by
    apply Matrix.ext
    intro i j
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      ((universalTargetAction (d := d)).coeff g).toRingEquiv _).symm
  rw [he] at hc
  exact semilinear_matrix_image_covariant E _ (A.map φ)
    (((universalTargetAction (d := d)).matrix g).map φ) hc hw

end Froberg
