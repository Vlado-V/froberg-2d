module

public import Froberg.ProjectedHomologyCoefficients

@[expose] public section

/-! Canonical scalar multiplication from the degree-d generator quotient
into the actual projected endpoint cokernel. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {Z : Type*} [AddCommGroup Z] [Module K Z]
variable {n d r : ℕ}

/-- Actual multiplication followed by the fixed target projection and quotient. -/
def projectedProduct (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) :
    Forms K n d →ₗ[K] Forms K n d →ₗ[K] ProjectedEndpointCokernel pi q where
  toFun z := (projectedEndpointMultiplication pi q).range.mkQ.comp (pi.comp (mulForm z))
  map_add' z w := by
    apply LinearMap.ext
    intro a
    have hm : mulForm (z+w) a=mulForm z a+mulForm w a :=
      Subtype.ext (add_mul z.val w.val a.val)
    simp only [LinearMap.comp_apply,LinearMap.add_apply,hm,map_add]
  map_smul' c z := by
    apply LinearMap.ext
    intro a
    have hm : mulForm (c • z) a=c • mulForm z a :=
      Subtype.ext (smul_mul_assoc c z.val a.val)
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,RingHom.id_apply,hm,map_smul]

/-- Every degree-d generator relation vanishes in the projected product. -/
theorem span_generators_le_projectedProduct_kernel
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (z : Forms K n d) :
    Submodule.span K (Set.range q) ≤ (projectedProduct pi q z).ker := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change (projectedEndpointMultiplication pi q).range.mkQ (pi (mulForm z (q i))) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨Pi.single i z,?_⟩
  change pi (endpointMultiplication q (Pi.single i z)) = _
  congr 1
  apply Subtype.ext
  simp only [endpointMultiplication_val,Pi.single_apply,apply_ite,Submodule.coe_zero,
    mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact mul_comm _ _

/-- The canonical quotient multiplication; no compatibility hypothesis is used. -/
def projectedQuotientProduct (pi : Forms K n (2*d) →ₗ[K] Z)
    (q : Fin r → Forms K n d) :
    Forms K n d →ₗ[K] (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K]
      ProjectedEndpointCokernel pi q where
  toFun z := (Submodule.span K (Set.range q)).liftQ (projectedProduct pi q z)
    (span_generators_le_projectedProduct_kernel pi q z)
  map_add' z w := by
    apply LinearMap.ext
    intro a
    obtain ⟨a,rfl⟩ := (Submodule.span K (Set.range q)).mkQ_surjective a
    exact LinearMap.congr_fun ((projectedProduct pi q).map_add z w) a
  map_smul' c z := by
    apply LinearMap.ext
    intro a
    obtain ⟨a,rfl⟩ := (Submodule.span K (Set.range q)).mkQ_surjective a
    exact LinearMap.congr_fun ((projectedProduct pi q).map_smul c z) a

@[simp] theorem projectedQuotientProduct_mk (pi : Forms K n (2*d) →ₗ[K] Z)
    (q : Fin r → Forms K n d) (z a : Forms K n d) :
    projectedQuotientProduct pi q z ((Submodule.span K (Set.range q)).mkQ a) =
      (projectedEndpointMultiplication pi q).range.mkQ (pi (mulForm z a)) := rfl

/-- The first normal map is the canonical quotient multiplication of its
faithfully extracted coefficients. -/
theorem projectedNormalMap_canonical_coefficient_formula
    [Infinite K] [FiniteDimensional K Z] {t : ℕ}
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (dual : Fin t → Forms K n d →ₗ[K] K) (z : Fin t → Forms K n d) :
    projectedNormalMap pi q (relativeGeneratorMotion q dual z) =
      (coefficientResponse (Submodule.span K (Set.range q)) (projectedQuotientProduct pi q) z).comp
        (projectedHomologyCoefficients pi q hq (Submodule.span K (Set.range q)) dual) := by
  have h := projectedNormalMap_coefficient_formula pi q hq
    (Submodule.span K (Set.range q)) (fun j => Submodule.subset_span ⟨j,rfl⟩)
    dual (projectedQuotientProduct pi q) (LinearMap.id : ProjectedEndpointCokernel pi q →ₗ[K] _)
    (fun _ _ => rfl) z
  exact h

end Froberg
