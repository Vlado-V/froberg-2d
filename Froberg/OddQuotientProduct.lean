import Froberg.ParityCoefficients
import Froberg.ProjectedQuotientMultiplication

/-! The odd source and target of scalar contraction as literal subspaces
of the degree-d and degree-2d generator quotients. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K : Type} [Field K] {n d r : ℕ}

abbrev generatorQuotient (q : Fin r → Forms K n d) :=
  Forms K n d ⧸ Submodule.span K (Set.range q)

def oddCoefficientSpace (w : Fin n → ZMod 2) (q : Fin r → Forms K n d) :
    Submodule K (generatorQuotient q) :=
  ((Submodule.span K (Set.range q)).mkQ.comp (parityForm w 1)).range

def oddTargetSpace (w : Fin n → ZMod 2) (q : Fin r → Forms K n d) :
    Submodule K (ProjectedEndpointCokernel (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q) :=
  ((projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ.comp
    (parityForm w 1)).range

/-- This is the same odd quotient used by the actual coefficient map. -/
theorem oddCoefficientSpace_eq_range
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) :
    oddCoefficientSpace w q=(parityGeneratorQuotient w e q hq 1).range := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(Submodule.span K (Set.range q)).mkQ a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨v,rfl⟩ := (Submodule.span K (Set.range q)).mkQ_surjective a
    exact ⟨v,rfl⟩

variable {P : Type*} [AddCommGroup P] [Module K P]

/-- Even multipliers send the actual odd quotient into the actual odd target. -/
theorem projectedQuotientProduct_mem_odd
    (w : Fin n → ZMod 2) (q : Fin r → Forms K n d)
    (f : Forms K n d) (hf : f.val.IsWeightedHomogeneous w 0)
    (a : oddCoefficientSpace w q) :
    projectedQuotientProduct (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q f a.val∈oddTargetSpace w q := by
  obtain ⟨v,hv⟩ := a.property
  rw [← hv]
  refine ⟨mulForm f (parityForm w 1 v),?_⟩
  change (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
    (parityForm w 1 (mulForm f (parityForm w 1 v))) = _
  rw [parityForm_mul w 1 0 _ _ hf]
  simp only [sub_zero,parityForm_same w 1 _ (parityForm_homogeneous w 1 v)]
  rfl

/-- The scalar contraction bilinear map with no substituted source or target. -/
def oddQuotientProduct
    (w : Fin n → ZMod 2) (q : Fin r → Forms K n d)
    (F : P →ₗ[K] Forms K n d) (hF : ∀ p,(F p).val.IsWeightedHomogeneous w 0) :
    P →ₗ[K] oddCoefficientSpace w q →ₗ[K] oddTargetSpace w q where
  toFun p := ((projectedQuotientProduct (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q (F p)).comp
    (oddCoefficientSpace w q).subtype).codRestrict _ (projectedQuotientProduct_mem_odd w q (F p) (hF p))
  map_add' p p' := by ext a; simp only [map_add,LinearMap.add_apply]; rfl
  map_smul' c p := by ext a; simp only [map_smul,LinearMap.smul_apply,RingHom.id_apply]; rfl

@[simp] theorem oddQuotientProduct_val
    (w : Fin n → ZMod 2) (q : Fin r → Forms K n d)
    (F : P →ₗ[K] Forms K n d) (hF : ∀ p,(F p).val.IsWeightedHomogeneous w 0)
    (p : P) (a : oddCoefficientSpace w q) :
    (oddQuotientProduct w q F hF p a).val=
      projectedQuotientProduct (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q (F p) a.val := rfl

end Froberg
