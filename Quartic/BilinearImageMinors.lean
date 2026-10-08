import Quartic.BilinearImage
import Quartic.KernelCharts
import Quartic.HomogeneousEmptyFiberOpen

/-!
# Homogeneous minors of actual bilinear image matrices

These lemmas connect the polynomial equations for a rank drop to the actual
bilinear image. No subspace encoding or openness conclusion is assumed here.
-/
noncomputable section
namespace Quartic.BilinearImageMinors
open Module Matrix MvPolynomial
variable {K : Type*} [Field K] {a b t d e s : ℕ} {I : Type*}

/-- Columns are the products of coefficient basis vectors with the given tuple. -/
def imageMatrix (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (v : Fin d → Fin a → K) : Matrix (Fin t) (Fin d × Fin b) K :=
  fun k j => mu (Pi.single j.2 1) (v j.1) k

/-- Matrix rank is the dimension of the full bilinear image of the tuple span. -/
theorem imageMatrix_rank (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (v : Fin d → Fin a → K) :
    (imageMatrix mu v).rank =
      finrank K (BilinearImage.image mu (Submodule.span K (Set.range v))) := by
  rw [BilinearImage.image_span_basis (Pi.basisFun K (Fin b)), Matrix.rank_eq_finrank_span_cols]
  have hc : (imageMatrix mu v).col =
      fun j : Fin d × Fin b => mu (Pi.basisFun K (Fin b) j.2) (v j.1) := by
    funext j
    change mu (Pi.single j.2 1) (v j.1) = mu (Pi.basisFun K (Fin b) j.2) (v j.1)
    simp only [Pi.basisFun_apply]
  rw [hc]

/-- Rank below e is exactly vanishing of every e-by-e minor, also for e=0. -/
theorem rank_lt_iff_minors_zero {R C : Type*} [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] (A : Matrix R C K) (e : ℕ) :
    A.rank < e ↔ ∀ u : Fin e → R, ∀ v : Fin e → C, (A.submatrix u v).det = 0 := by
  classical
  constructor
  · intro h u v
    by_contra hn
    have hr := Matrix.rank_submatrix_le A u v
    rw [Matrix.rank_of_det_ne_zero hn, Fintype.card_fin] at hr
    omega
  · intro h
    by_contra hn
    let A' := A.submatrix (Fintype.equivFin R).symm (Fintype.equivFin C).symm
    have he : e ≤ A'.rank := by
      rw [show A'.rank = A.rank from Matrix.rank_submatrix _ _ _]
      omega
    obtain ⟨u,v,huv⟩ := KernelCharts.exists_minor_of_rank_le A' he
    apply huv
    exact h ((Fintype.equivFin R).symm ∘ u) ((Fintype.equivFin C).symm ∘ v)

/-- Different columns may carry different homogeneous degrees. -/
theorem determinant_homogeneous {σ : Type*} (M : Matrix (Fin e) (Fin e) (MvPolynomial σ K))
    (degrees : Fin e → ℕ) (hM : ∀ i j, (M i j).IsHomogeneous (degrees j)) :
    M.det.IsHomogeneous (∑ j, degrees j) := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro perm _
  have hprod := IsHomogeneous.prod Finset.univ (fun i => M (perm i) i) degrees
    (fun i _ => hM (perm i) i)
  simpa only [map_intCast] using hprod.C_mul ((Equiv.Perm.sign perm : ℤ) : K)

/-- A determinant with linear homogeneous entries has degree its size. -/
theorem determinant_homogeneous_one {σ : Type*}
    (M : Matrix (Fin e) (Fin e) (MvPolynomial σ K))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous e := by
  simpa using determinant_homogeneous M (fun _ => 1) hM

/-- Multiplication as a bilinear map between the actual homogeneous pieces. -/
def formMul (m n : ℕ) : Forms K s m →ₗ[K] Forms K s n →ₗ[K] Forms K s (m+n) where
  toFun f :=
    { toFun g := ⟨f.val*g.val, f.property.mul g.property⟩
      map_add' g h := Subtype.ext (mul_add _ _ _)
      map_smul' c g := Subtype.ext (mul_smul_comm _ _ _) }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    exact add_mul _ _ _
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    exact smul_mul_assoc _ _ _

/-- Product of e linear homogeneous forms. -/
def productOne (f : Fin e → Forms K s 1) : Forms K s e :=
  ⟨∏ i, (f i).val, by
    simpa using IsHomogeneous.prod Finset.univ (fun i => (f i).val) (fun _ => 1)
      (fun i _ => (f i).property)⟩

/-- Products of finitely many polynomial linear-form families remain polynomial. -/
theorem productOne_polynomial (f : Fin e → (I → K) → Forms K s 1)
    (hf : ∀ i, IsPolynomialFamily (f i)) :
    IsPolynomialFamily (fun p => productOne (fun i => f i p)) := by
  induction e with
  | zero =>
    convert isPolynomialFamily_const (ι := I) (productOne (fun i : Fin 0 => f i (fun _ => 0))) using 1
    funext p
    apply Subtype.ext
    simp [productOne]
  | succ e ih =>
    have hp := ih (fun i => f i.succ) (fun i => hf i.succ)
    have hm := hp.bilinear (hf 0) (formMul e 1)
    convert hm using 1
    funext p
    apply Subtype.ext
    simp only [productOne, formMul, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.prod_univ_succ, mul_comm]

/-- The actual determinant, bundled in its homogeneous target space. -/
def determinantForm (M : Matrix (Fin e) (Fin e) (Forms K s 1)) : Forms K s e :=
  ⟨Matrix.det (fun i j => (M i j).val), determinant_homogeneous_one _ (fun i j => (M i j).property)⟩

/-- Determinant equations vary polynomially with all actual linear-form entries. -/
theorem determinantForm_polynomial
    (M : (I → K) → Matrix (Fin e) (Fin e) (Forms K s 1))
    (hM : ∀ i j, IsPolynomialFamily (fun p => M p i j)) :
    IsPolynomialFamily (fun p => determinantForm (M p)) := by
  classical
  have h := IsPolynomialFamily.sum (fun perm : Equiv.Perm (Fin e) =>
    (isPolynomialFamily_const (ι := I) ((Equiv.Perm.sign perm : ℤ) : K)).smul
      (productOne_polynomial (fun i p => M p (perm i) i) (fun i => hM (perm i) i)))
  convert h using 1
  funext p
  apply Subtype.ext
  simp only [determinantForm, Submodule.coe_sum, Submodule.coe_smul,
    productOne, smul_eq_C_mul, map_intCast]
  exact Matrix.det_apply' _

end Quartic.BilinearImageMinors
