module

public import Quartic.ThreeBlockModel

@[expose] public section

/-!
# The actual pure quadratic quotient and its two coordinates

The coefficient reduction has precisely the span of the four block quadrics
as its kernel. It therefore gives coordinates on the genuine homogeneous
quadratic quotient, with `x²`, `y²`, `z²` mapping to `(1,0)`, `(0,1)`, `(-1,-1)`.
-/

noncomputable section
namespace Quartic.ThreeBlockQuotient
open Module MvPolynomial ThreeBlock ThreeBlockModel
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

/-- The actual pure quadratic relations, inside the degree-two component. -/
def pureSpace : Submodule K (Forms K 3 2) :=
  Submodule.span K (Set.range (blockQuadrics (K := K)))

abbrev PureQuotient (K : Type*) [Field K] := Forms K 3 2 ⧸ pureSpace (K := K)

/-- Coefficient reduction in the displayed basis `(x²,y²)`. -/
def reduction : Forms K 3 2 →ₗ[K] K × K :=
  (((lcoeff K (Finsupp.single (0 : Fin 3) 2)) - (lcoeff K (Finsupp.single (2 : Fin 3) 2))).prod
    ((lcoeff K (Finsupp.single (1 : Fin 3) 2)) - (lcoeff K (Finsupp.single (2 : Fin 3) 2)))).comp
      (Forms K 3 2).subtype

theorem reduction_eq (f : Forms K 3 2) :
    reduction f = (quadraticReduction f.val 0, quadraticReduction f.val 1) := rfl

/-- Each coordinate square is an actual homogeneous quadratic. -/
def square (i : Fin 3) : Forms K 3 2 := ⟨X i ^ 2, isHomogeneous_X_pow i 2⟩

set_option maxRecDepth 4096 in
theorem reduction_square (i : Fin 3) :
    reduction (square (K := K) i) =
      if i = 0 then (1, 0) else if i = 1 then (0, 1) else (-1, -1) := by
  fin_cases i <;>
    norm_num [reduction, square, lcoeff, MvPolynomial.X, pow_two,
      monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]

@[simp] theorem reduction_square_zero : reduction (square (K := K) 0) = (1, 0) := by
  simp [reduction_square]
@[simp] theorem reduction_square_one : reduction (square (K := K) 1) = (0, 1) := by
  simp [reduction_square]
@[simp] theorem reduction_square_two : reduction (square (K := K) 2) = (-1, -1) := by
  simp [reduction_square]

theorem reduction_quadric (i : Fin 4) : reduction (blockQuadrics (K := K) i) = 0 := by
  rw [reduction_eq, blockQuadrics_val, quadraticReduction_quadric]
  rfl

theorem pureSpace_le_ker : pureSpace (K := K) ≤ LinearMap.ker reduction := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact reduction_quadric i

theorem reduction_surjective : Function.Surjective (reduction (K := K)) := by
  rintro ⟨a, b⟩
  refine ⟨a • square 0 + b • square 1, ?_⟩
  simp

theorem pureSpace_finrank : finrank K (pureSpace (K := K)) = 4 := by
  change finrank K (Submodule.span K (Set.range (blockQuadrics (K := K)))) = Fintype.card (Fin 4)
  exact finrank_span_eq_card (blockQuadrics_independent (K := K))

/-- The coordinate kernel consists of exactly the four actual pure relations. -/
theorem reduction_ker : LinearMap.ker (reduction (K := K)) = pureSpace := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq pureSpace_le_ker
  have hd := (reduction (K := K)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr reduction_surjective, finrank_top] at hd
  norm_num [Module.finrank_prod, finrank_quadrics, Nat.choose] at hd
  rw [pureSpace_finrank]
  omega

def quotientCoordinates {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (B : Submodule K V)
    (hk : f.ker = B) (hs : Function.Surjective f) : (V ⧸ B) ≃ₗ[K] W :=
  (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)

private theorem quotientCoordinates_mk {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (B : Submodule K V)
    (hk : f.ker = B) (hs : Function.Surjective f) (v : V) :
    quotientCoordinates f B hk hs (Submodule.Quotient.mk v) = f v := by
  simp [quotientCoordinates]

/-- The genuine pure quadratic quotient in the manuscript's displayed coordinates. -/
def quotientEquiv : PureQuotient K ≃ₗ[K] K × K :=
  quotientCoordinates reduction pureSpace reduction_ker reduction_surjective

@[simp] theorem quotientEquiv_mk (f : Forms K 3 2) :
    quotientEquiv (Submodule.Quotient.mk f : PureQuotient K) = reduction f := by
  rfl

@[simp] theorem quotientEquiv_x_square :
    quotientEquiv (Submodule.Quotient.mk (square (K := K) 0) : PureQuotient K) = (1, 0) := by
  simp
@[simp] theorem quotientEquiv_y_square :
    quotientEquiv (Submodule.Quotient.mk (square (K := K) 1) : PureQuotient K) = (0, 1) := by
  simp
@[simp] theorem quotientEquiv_z_square :
    quotientEquiv (Submodule.Quotient.mk (square (K := K) 2) : PureQuotient K) = (-1, -1) := by
  simp

theorem pureQuotient_finrank : finrank K (PureQuotient K) = 2 := by
  rw [(quotientEquiv (K := K)).finrank_eq]
  simp

end Quartic.ThreeBlockQuotient
