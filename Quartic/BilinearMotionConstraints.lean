module

public import Quartic.CoefficientConstraintRank

@[expose] public section

/-!
# Actual polynomial motion constraints and their ranks

A spanning family of coefficient vectors, including one depending on earlier
motions, gives explicit equations on the next motions. Their matrix rank is
the rank of the repeated covector relation map on the coefficient span.
Thus the codimension bound follows from the actual span dimension; the
spanning columns need not be independent or form a chosen quotient basis.
-/
noncomputable section
namespace Quartic.BilinearMotionConstraints
open Module Matrix MvPolynomial BilinearCoefficientKernel BilinearCovectorCharts
variable {K I N : Type*} [Field K] [Fintype N] {a b T c : ℕ}

/-- Flatten coefficient components without changing any field coordinates. -/
def flatten : (Fin c → Fin b → K) ≃ₗ[K] (Fin c × Fin b → K) where
  toFun x z := x z.1 z.2
  invFun y i j := y (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equations on all c motion vectors, one row for each spanning coefficient vector. -/
def constraint (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (H : N → Fin c → Fin a → K) : Matrix N (Fin c × Fin b) K :=
  fun j z => covector ell (mu (Pi.single z.2 1) (H j z.1))

 theorem rank_eq (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (H : N → Fin c → Fin a → K) :
    (constraint mu ell H).rank = finrank K
      ((Submodule.span K (Set.range H)).map (CoefficientConstraintRank.repeated (relationMap mu ell))) := by
  rw [← Matrix.rank_transpose,Matrix.rank_eq_finrank_span_cols]
  let R := CoefficientConstraintRank.repeated (c := c) (relationMap mu ell)
  have he : (constraint mu ell H).transpose.col = fun j => flatten (R (H j)) := rfl
  rw [he]
  have hs : Submodule.span K (Set.range (fun j => flatten (R (H j)))) =
      ((Submodule.span K (Set.range H)).map R).map flatten.toLinearMap := by
    rw [Submodule.map_span,Submodule.map_span,← Set.range_comp,← Set.range_comp]
    rfl
  rw [hs,LinearEquiv.finrank_map_eq]

/-- The actual motion conditions lose at most c times the covector kernel dimension. -/
theorem rank_bound (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (H : N → Fin c → Fin a → K) :
    finrank K (Submodule.span K (Set.range H)) - c * finrank K (LinearMap.ker (relationMap mu ell)) ≤
      (constraint mu ell H).rank := by
  rw [rank_eq]
  let S := Submodule.span K (Set.range H)
  have h := CoefficientConstraintRank.rank_bound (relationMap mu ell) S.subtype Subtype.val_injective
  rw [LinearMap.range_comp,Submodule.range_subtype] at h
  exact h

/-- Evaluation is the covector applied to the actual sum of motion products. -/
theorem mulVec_apply (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (H : N → Fin c → Fin a → K)
    (p : Fin c × Fin b → K) (j : N) :
    (constraint mu ell H *ᵥ p) j = covector ell (∑ i : Fin c, mu (fun f => p (i,f)) (H j i)) := by
  classical
  simp only [Matrix.mulVec,dotProduct,constraint,Fintype.sum_prod_type,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [← (Pi.basisFun K (Fin b)).sum_equivFun (fun f => p (i,f))]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    Pi.basisFun_apply,Pi.basisFun_equivFun,LinearEquiv.refl_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro f _
  ring

/-- Vanishing on the spanning columns is equivalent to vanishing on the
entire actual coefficient space. -/
theorem kernel_iff (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → K) (H : N → Fin c → Fin a → K) (p : Fin c × Fin b → K) :
    constraint mu ell H *ᵥ p = 0 ↔
      ∀ x ∈ Submodule.span K (Set.range H), covector ell (∑ i : Fin c, mu (fun f => p (i,f)) (x i)) = 0 := by
  classical
  let L : (Fin c → Fin a → K) →ₗ[K] K :=
    ∑ i, (covector ell).comp ((mu (fun f => p (i,f))).comp (LinearMap.proj i))
  have hL (x : Fin c → Fin a → K) : L x = covector ell (∑ i, mu (fun f => p (i,f)) (x i)) := by
    simp [L]
  constructor
  · intro h x hx
    have hspan : Submodule.span K (Set.range H) ≤ LinearMap.ker L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change L (H j) = 0
      rw [hL,← mulVec_apply]
      exact congrFun h j
    exact (hL x).symm.trans (hspan hx)
  · intro h
    funext j
    rw [mulVec_apply]
    exact h _ (Submodule.subset_span ⟨j,rfl⟩)

/-- Literal polynomial equations for moving coefficient vectors and a
covector represented by polynomial numerators. -/
def polynomialConstraint
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → MvPolynomial I K) (H : N → Fin c → Fin a → MvPolynomial I K) :
    Matrix N (Fin c × Fin b) (MvPolynomial I K) :=
  fun j z => ∑ v : Fin a, ∑ k : Fin T,
    H j z.1 v * ell k * C (mu (Pi.single z.2 1) (Pi.single v 1) k)

 theorem eval_polynomialConstraint
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ell : Fin T → MvPolynomial I K) (H : N → Fin c → Fin a → MvPolynomial I K)
    (p : I → K) :
    (polynomialConstraint mu ell H).map (eval p) =
      constraint mu (fun k => eval p (ell k)) (fun j i v => eval p (H j i v)) := by
  classical
  ext j z
  change eval p (∑ v : Fin a, ∑ k : Fin T,
    H j z.1 v * ell k * C (mu (Pi.single z.2 1) (Pi.single v 1) k)) = _
  unfold constraint
  dsimp only
  conv_rhs => rw [← (Pi.basisFun K (Fin a)).sum_equivFun (fun v => eval p (H j z.1 v))]
  simp only [map_sum,map_mul,eval_C,map_smul,covector_apply,
    Pi.basisFun_apply,Pi.basisFun_equivFun,LinearEquiv.refl_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Quartic.BilinearMotionConstraints
