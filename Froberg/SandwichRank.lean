module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic

@[expose] public section

/-! Exact rank of the linear equations C P A=0 on a varying projection P.
This supplies the Schubert codimension calculation used in C.3. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K U V W Z : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

/-- The literal sandwich equations on a varying linear map. -/
def sandwichMap (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    (V →ₗ[K] W) →ₗ[K] (U →ₗ[K] Z) where
  toFun P := C.comp (P.comp A)
  map_add' P Q := by ext u; simp
  map_smul' c P := by ext u; simp

/-- First restrict to the image of A and corestrict through the image of C. -/
def restrictedSandwich (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    (V →ₗ[K] W) →ₗ[K] (A.range →ₗ[K] C.range) where
  toFun P := C.rangeRestrict.comp (P.comp A.range.subtype)
  map_add' P Q := by ext u; simp
  map_smul' c P := by ext u; simp

/-- Every map between the two image spaces is realized by an actual P. -/
theorem restrictedSandwich_surjective (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    Function.Surjective (restrictedSandwich A C) := by
  obtain ⟨p,hp⟩ := A.range.subtype.exists_leftInverse_of_injective A.range.ker_subtype
  obtain ⟨s,hs⟩ := C.rangeRestrict.exists_rightInverse_of_surjective C.range_rangeRestrict
  intro F
  refine ⟨s.comp (F.comp p),?_⟩
  apply LinearMap.ext
  intro u
  change C.rangeRestrict (s (F (p u.val))) = F u
  have hp' : p u.val = u := LinearMap.congr_fun hp u
  have hs' : C.rangeRestrict (s (F u)) = F u := LinearMap.congr_fun hs (F u)
  rw [hp',hs']

/-- Inflation back to the ambient source and target loses no information. -/
def inflateSandwich (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    (A.range →ₗ[K] C.range) →ₗ[K] (U →ₗ[K] Z) where
  toFun F := C.range.subtype.comp (F.comp A.rangeRestrict)
  map_add' P Q := by ext u; simp
  map_smul' c P := by ext u; simp

theorem inflateSandwich_injective (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    Function.Injective (inflateSandwich A C) := by
  intro F G h
  apply LinearMap.ext
  intro u
  obtain ⟨v,rfl⟩ := (LinearMap.range_eq_top.mp A.range_rangeRestrict) u
  apply Subtype.ext
  exact LinearMap.congr_fun h v

theorem sandwichMap_factorization (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    sandwichMap A C = (inflateSandwich A C).comp (restrictedSandwich A C) := rfl

/-- The codimension of C P A=0 is rank(A)rank(C), with no general-position
or surjectivity assumption on A or C. -/
theorem sandwichMap_rank [FiniteDimensional K V] [FiniteDimensional K W]
    (A : U →ₗ[K] V) (C : W →ₗ[K] Z) :
    finrank K (sandwichMap A C).range = finrank K A.range * finrank K C.range := by
  rw [sandwichMap_factorization,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (restrictedSandwich_surjective A C),Submodule.map_top,
    LinearMap.finrank_range_of_inj (inflateSandwich_injective A C),Module.finrank_linearMap]

end Froberg
