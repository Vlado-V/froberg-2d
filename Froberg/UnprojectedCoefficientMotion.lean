import Froberg.HomologyCoefficientMotion

/-! Compatibility of the unprojected normal map with actual homology coefficients. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module
variable {K : Type} [Field K] {n d r t : ℕ}

@[simp] theorem homologyFormalRepresentative_mk (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (a : (endpointMultiplication q).ker) :
    homologyFormalRepresentative htwo q hq (kernelClass (endpointMultiplication q) (koszulSpace q) a) =
      formalCoefficientMap q a.val := by
  rfl

/-- Explicit coefficient map on actual homology, before the retained quotient. -/
def actualHomologyCoefficients (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (G : Submodule K (Forms K n d)) (dual : Fin t → Forms K n d →ₗ[K] K) :
    EndpointHomology q →ₗ[K] (Fin t → Forms K n d ⧸ G) :=
  (relationCoefficientMap G dual).comp (homologyFormalRepresentative htwo q hq)

@[simp] theorem actualHomologyCoefficients_mk (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (G : Submodule K (Forms K n d)) (hqG : ∀ j, q j ∈ G)
    (dual : Fin t → Forms K n d →ₗ[K] K) (a : (endpointMultiplication q).ker) :
    actualHomologyCoefficients htwo q hq G dual (kernelClass (endpointMultiplication q) (koszulSpace q) a) =
      fun i => ∑ j, dual i (q j) • G.mkQ (a.val j) := by
  rw [actualHomologyCoefficients,LinearMap.comp_apply,homologyFormalRepresentative_mk]
  exact relationCoefficientMap_general_coefficients G q hqG dual a.val

/-- The relative coefficient map has exactly the naturally retained kernel. -/
theorem actualHomologyCoefficients_kernel (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hspan : Submodule.span K (Set.range q) = W ⊔ Submodule.span K (Set.range f))
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map formalPolynomialMultiplication).comap
        (formalPolynomialMultiplication (K := K) (n := n) (d := d)) = ⊥) :
    (actualHomologyCoefficients htwo q hq (W ⊔ Submodule.span K (Set.range f)) dual).ker =
      retainedHomology htwo q hq W :=
  homology_coefficient_kernel htwo q hq W f hspan dual hdualW hdualF hsep

/-- The first normal map is literally scalar multiplication of the extracted
coefficients. The compatibility premise is only the defining product formula
for the chosen target quotient. -/
theorem endpointNormalMap_coefficient_formula {J : Type*} [AddCommGroup J] [Module K J]
    (htwo : (2 : K) ≠ 0) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (G : Submodule K (Forms K n d)) (hqG : ∀ j, q j ∈ G)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (mu : Forms K n d →ₗ[K] (Forms K n d ⧸ G) →ₗ[K] J)
    (pi : EndpointCokernel q →ₗ[K] J)
    (hmu : ∀ z a, mu z (G.mkQ a) = pi (cokernelClass (endpointMultiplication q) (mulForm z a)))
    (z : Fin t → Forms K n d) :
    pi.comp (endpointNormalMap q (relativeGeneratorMotion q dual z)) =
      (coefficientResponse G mu z).comp (actualHomologyCoefficients htwo q hq G dual) := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,rfl⟩ := kernelClass_surjective (endpointMultiplication q) (koszulSpace q) x
  rw [LinearMap.comp_apply,LinearMap.comp_apply,actualHomologyCoefficients_mk htwo q hq G hqG]
  rw [coefficientResponse_apply]
  change pi (cokernelClass (endpointMultiplication q)
    (endpointMultiplication (relativeGeneratorMotion q dual z) a.val)) = _
  have hp : endpointMultiplication (relativeGeneratorMotion q dual z) a.val =
      ∑ j, ∑ i, dual i (q j) • mulForm (z i) (a.val j) := by
    apply Subtype.ext
    simp [endpointMultiplication_val,relativeGeneratorMotion,Finset.sum_mul,mulForm]
  rw [hp]
  simp only [map_sum,map_smul,hmu]
  rw [Finset.sum_comm]

end Froberg
