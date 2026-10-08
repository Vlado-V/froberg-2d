import Froberg.ParityCoefficients
import Froberg.BilinearScalarSurjection

/-! Intrinsic coordinates on the actual odd coefficient quotient preserve
the full coefficient kernel of projected homology. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Quartic.PolynomialBilinearCoordinates

/-- Coordinates in the genuine image of a linear projection. -/
def rangeCoordinateMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (P : V →ₗ[K] V) : V →ₗ[K] (Fin (finrank K P.range) → K) :=
  (coordinates K P.range).toLinearMap.comp P.rangeRestrict

theorem rangeCoordinateMap_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (P : V →ₗ[K] V) (v : V) :
    rangeCoordinateMap P v=0 ↔ P v=0 := by
  change coordinates K P.range (P.rangeRestrict v)=0 ↔ P v=0
  rw [LinearEquiv.map_eq_zero_iff]
  exact Subtype.ext_iff

variable {K : Type} [Field K] {n d r t : ℕ}
variable {Z : Type*} [AddCommGroup Z] [Module K Z]

/-- The coefficient map into odd coordinates has exactly the original
retained kernel; no dimension is lost by using those coordinates in C.6. -/
theorem projected_coefficients_odd_coordinates_kernel
    (htwo : (2 : K) ≠ 0)
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hi : LinearIndependent K q)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z,pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous w (1-e i)) → a.val∈oppositeKoszulSpace q e)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdual : ∀ i j,e j=0 → dual i (q j)=0) :
    (((rangeCoordinateMap (parityGeneratorQuotient w e q hq 1)).compLeft (Fin t)).comp
      (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual)).ker =
      (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual).ker := by
  ext x
  constructor
  · intro hx
    change projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual x=0
    funext i
    have hzero : rangeCoordinateMap (parityGeneratorQuotient w e q hq 1)
        (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual x i)=0 :=
      congrFun hx i
    rw [rangeCoordinateMap_eq_zero,
      projectedHomologyCoefficients_odd htwo w e q hi hq pi hpi hodd dual hdual x i] at hzero
    exact hzero
  · intro hx
    change ((rangeCoordinateMap (parityGeneratorQuotient w e q hq 1)).compLeft (Fin t))
      (projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual x)=0
    rw [show projectedHomologyCoefficients htwo pi q hi (Submodule.span K (Set.range q)) dual x=0 from hx,
      map_zero]

end Froberg
