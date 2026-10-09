module

public import Froberg.GenericFractionRank
public import Froberg.MatrixRankBaseChange

@[expose] public section

/-! # Field-extension invariance of the actual generic endpoint defects

The coefficient transport and monomial-basis argument is adapted from
`Quartic/GenericFieldDescent.lean` in the user's existing development.
-/

noncomputable section
namespace Froberg.GenericFieldDescent
open Module Matrix MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {K L : Type*} [Field K] [Field L] {n d r : ℕ}

private theorem basis_transport_repr {V I : Type*} [AddCommGroup V] [Module K V]
    (P Q : Submodule K V) (h : P = Q) (b : Basis I K Q) (T : I → V → K)
    (hb : ∀ p i, b.repr p i = T i p.val) (p : P) (i : I) :
    ((congrArg (fun S : Submodule K V => Basis I K S) h).mpr b).repr p i = T i p.val := by
  subst Q
  exact hb p i

theorem formsBasis_equivFun_coeff (p : Forms K n d) (s : Sym (Fin n) d) :
    (formsBasis K n d).equivFun p s = p.val.coeff (exponentEquiv n d s).val := by
  rw [Basis.equivFun_apply]
  simpa only [formsBasis, eq_mpr_eq_cast, cast_cast] using
    basis_transport_repr (Forms K n d) _
      (homogeneousSubmodule_eq_finsupp_supported (Fin n) K d)
      ((basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
        (exponentEquiv n d).symm)
      (fun s p => p.coeff (exponentEquiv n d s).val) (fun _ _ => rfl) p s

def mapForm (f : K →+* L) (p : Forms K n d) : Forms L n d :=
  ⟨MvPolynomial.map f p.val, p.property.map f⟩

@[simp] theorem mapForm_coordinates (f : K →+* L) (p : Forms K n d)
    (s : Sym (Fin n) d) :
    (formsBasis L n d).equivFun (mapForm f p) s =
      f ((formsBasis K n d).equivFun p s) := by
  simp only [formsBasis_equivFun_coeff, mapForm, coeff_map]

theorem coefficientForms_map (f : K →+* L) (a : CoefficientIndex n d r → K)
    (i : Fin r) : mapForm f (coefficientForms K n d r a i) =
      coefficientForms L n d r (fun j => f (a j)) i := by
  apply (formsBasis L n d).equivFun.injective
  funext s
  rw [mapForm_coordinates]
  simp only [coefficientForms, LinearEquiv.apply_symm_apply]

def multiplierBasis : Basis (CoefficientIndex n d r) K (Fin r → Forms K n d) :=
  Basis.ofEquivFun coefficientCoordinates

theorem multiplierBasis_apply (j : CoefficientIndex n d r) :
    multiplierBasis (K := K) j = coefficientForms K n d r (Pi.single j 1) := by
  apply coefficientCoordinates.injective
  change (multiplierBasis (K := K)).equivFun (multiplierBasis j) = _
  funext i
  rw [Basis.equivFun_self]
  change (if j = i then 1 else 0) = (formsBasis K n d).equivFun
    ((formsBasis K n d).equivFun.symm
      (fun b => (Pi.single j (1 : K) : CoefficientIndex n d r → K) (i.1, b))) i.2
  simp only [LinearEquiv.apply_symm_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem multiplierBasis_map (f : K →+* L) (j : CoefficientIndex n d r) (i : Fin r) :
    mapForm f (multiplierBasis (K := K) j i) = multiplierBasis (K := L) j i := by
  classical
  rw [multiplierBasis_apply, multiplierBasis_apply, coefficientForms_map]
  congr 2
  funext x
  simp [Pi.single_apply]

theorem endpointMultiplication_map (f : K →+* L) (q a : Fin r → Forms K n d) :
    mapForm f (endpointMultiplication q a) =
      endpointMultiplication (fun i => mapForm f (q i)) (fun i => mapForm f (a i)) := by
  apply Subtype.ext
  simp only [mapForm, endpointMultiplication_val, map_sum, map_mul]

def multiplicationMatrixLinear : (CoefficientIndex n d r → K) →ₗ[K]
    Matrix (Sym (Fin n) (2 * d)) (CoefficientIndex n d r) K :=
  (LinearMap.toMatrix multiplierBasis (formsBasis K n (2 * d))).toLinearMap.comp
    coefficientMultiplicationLinear

theorem multiplicationMatrix_map (f : K →+* L) (a : CoefficientIndex n d r → K) :
    (multiplicationMatrixLinear a).map f =
      multiplicationMatrixLinear (fun j => f (a j)) := by
  funext row col
  change f (LinearMap.toMatrix (multiplierBasis (K := K)) (formsBasis K n (2 * d))
    (endpointMultiplication (coefficientForms K n d r a)) row col) =
      LinearMap.toMatrix (multiplierBasis (K := L)) (formsBasis L n (2 * d))
        (endpointMultiplication (coefficientForms L n d r (fun j => f (a j)))) row col
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  rw [← Basis.equivFun_apply, ← Basis.equivFun_apply, ← mapForm_coordinates,
    endpointMultiplication_map]
  have hq := funext (coefficientForms_map f a)
  have ha := funext (multiplierBasis_map f col)
  rw [hq, ha]

def multiplicationEntryLinear (row : Sym (Fin n) (2 * d)) (col : CoefficientIndex n d r) :
    (CoefficientIndex n d r → K) →ₗ[K] K where
  toFun a := multiplicationMatrixLinear a row col
  map_add' a b := by simp
  map_smul' c a := by simp

def monomialMultiplicationMatrix : Matrix (Sym (Fin n) (2 * d)) (CoefficientIndex n d r)
    (MvPolynomial (CoefficientIndex n d r) K) :=
  fun row col => polynomialOfLinear (multiplicationEntryLinear row col)

theorem monomialMultiplicationMatrix_eval (a : CoefficientIndex n d r → K) :
    (monomialMultiplicationMatrix (K := K)).map (eval a) = multiplicationMatrixLinear a := by
  ext row col
  exact eval_polynomialOfLinear (multiplicationEntryLinear row col) a

theorem multiplicationMatrix_rank (a : CoefficientIndex n d r → K) :
    (multiplicationMatrixLinear a).rank =
      finrank K (LinearMap.range (endpointMultiplication (coefficientForms K n d r a))) := by
  rw [Matrix.rank_eq_finrank_range_toLin (multiplicationMatrixLinear a)
    (formsBasis K n (2 * d)) multiplierBasis]
  change finrank K (LinearMap.range
    (Matrix.toLin multiplierBasis (formsBasis K n (2 * d))
      (LinearMap.toMatrix multiplierBasis (formsBasis K n (2 * d))
        (endpointMultiplication (coefficientForms K n d r a))))) = _
  rw [Matrix.toLin_toMatrix]

theorem monomialMultiplicationMatrix_map (f : K →+* L) :
    (monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)).map
      (MvPolynomial.map f) = monomialMultiplicationMatrix (K := L) := by
  classical
  funext row col
  change MvPolynomial.map f (polynomialOfLinear (multiplicationEntryLinear row col)) =
    polynomialOfLinear (multiplicationEntryLinear row col)
  simp only [polynomialOfLinear, map_sum, map_mul, map_C, map_X]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  have h := congrFun (congrFun (multiplicationMatrix_map f (Pi.single i 1)) row) col
  have he : (fun j => f ((Pi.single i (1 : K) : CoefficientIndex n d r → K) j)) =
      (Pi.single i (1 : L) : CoefficientIndex n d r → L) := by
    funext j
    simp [Pi.single_apply]
  rw [he] at h
  exact h

theorem genericCokernel_add_monomial_fraction_rank [Infinite K] (hn : 0 < n) :
    genericCokernel K n d r +
      ((monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)).map
        (algebraMap _ (FractionRing (MvPolynomial (CoefficientIndex n d r) K)))).rank =
      (n + 2 * d - 1).choose (2 * d) := by
  classical
  let F := FractionRing (MvPolynomial (CoefficientIndex n d r) K)
  let M := monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)
  obtain ⟨a, ha⟩ := exists_specialization_rank_eq_fraction_rank (F := F) M
  obtain ⟨a₀, ha₀⟩ := genericCokernel_attained K n d r
  have hrow (b : CoefficientIndex n d r → K) :
      coefficientCokernel K n d r b + (M.map (eval b)).rank =
        (n + 2 * d - 1).choose (2 * d) := by
    rw [show M = monomialMultiplicationMatrix from rfl,
      monomialMultiplicationMatrix_eval, multiplicationMatrix_rank]
    exact endpoint_quotient_add_rank hn (coefficientForms K n d r b)
  have hb := hrow a
  rw [ha] at hb
  have hb₀ := hrow a₀
  rw [ha₀] at hb₀
  have hmin := genericCokernel_le K n d r a
  have hmax := specialization_rank_le_fraction_rank (F := F) M a₀
  change genericCokernel K n d r + (M.map (algebraMap _ F)).rank = _
  dsimp only [F] at *
  omega

/-- The monomial-coordinate generic rank is unchanged by extending the field. -/
theorem monomial_fraction_rank_map (f : K →+* L) :
    ((monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)).map
      (algebraMap _ (FractionRing (MvPolynomial (CoefficientIndex n d r) K)))).rank =
    ((monomialMultiplicationMatrix (K := L) (n := n) (d := d) (r := r)).map
      (algebraMap _ (FractionRing (MvPolynomial (CoefficientIndex n d r) L)))).rank := by
  classical
  let FK := FractionRing (MvPolynomial (CoefficientIndex n d r) K)
  let FL := FractionRing (MvPolynomial (CoefficientIndex n d r) L)
  let ψ : FK →+* FL := IsFractionRing.map
    (MvPolynomial.map_injective (σ := CoefficientIndex n d r) f f.injective)
  have hψ (x : MvPolynomial (CoefficientIndex n d r) K) :
      ψ (algebraMap _ FK x) = algebraMap _ FL (MvPolynomial.map f x) := by
    simp only [ψ, IsFractionRing.map, IsLocalization.map_eq]
  have heq : (((monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)).map
      (algebraMap _ FK)).map ψ) =
      (monomialMultiplicationMatrix (K := L)).map (algebraMap _ FL) := by
    calc
      _ = ((monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)).map
          (MvPolynomial.map f)).map (algebraMap _ FL) := by
        apply Matrix.ext
        intro i j
        exact hψ _
      _ = _ := congrArg (fun M : Matrix (Sym (Fin n) (2 * d)) (CoefficientIndex n d r)
          (MvPolynomial (CoefficientIndex n d r) L) => M.map (algebraMap _ FL))
            (monomialMultiplicationMatrix_map f)
  have hr := matrix_rank_map_field ψ
    ((monomialMultiplicationMatrix (K := K) (n := n) (d := d) (r := r)).map (algebraMap _ FK))
  rw [heq] at hr
  exact hr.symm

/-- The attained generic cokernel dimension descends along any field
extension between infinite fields. -/
theorem genericCokernel_baseChange [Infinite K] [Infinite L]
    (f : K →+* L) (hn : 0 < n) :
    genericCokernel K n d r = genericCokernel L n d r := by
  have hK := genericCokernel_add_monomial_fraction_rank (K := K) (d := d) (r := r) hn
  have hL := genericCokernel_add_monomial_fraction_rank (K := L) (d := d) (r := r) hn
  have hr := monomial_fraction_rank_map (n := n) (d := d) (r := r) f
  omega

/-- The actual generic homology defect has the same field-extension
invariance, by its defining Euler relation. -/
theorem genericHomology_baseChange [Infinite K] [Infinite L]
    (f : K →+* L) (hn : 0 < n) :
    genericHomology K n d r = genericHomology L n d r := by
  unfold genericHomology
  rw [genericCokernel_baseChange f hn]

end Froberg.GenericFieldDescent
