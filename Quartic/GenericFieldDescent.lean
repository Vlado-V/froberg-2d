import Quartic.GenericMatrix
import Quartic.TraceTranspose
import Quartic.KernelCharts
import Quartic.PolynomialImageAvoidance

/-!
# Descent of actual generic quartic rank along field extensions

Coefficient transport is checked on actual homogeneous polynomials, the
monomial multiplier basis, and the resulting multiplication matrix.
Nonzero coefficient and multiplication minors at an extension-field witness
therefore give nonzero polynomials over the base field. Infinite base fields
have a common nonvanishing coefficient array, proving the original generic
quartic statement there. No scalar-extension rank or algebraicity premise
is assumed.
-/
noncomputable section
namespace Quartic.GenericFieldDescent
open Module MvPolynomial
variable {K L : Type*} [Field K] [Field L] {n d r : ℕ}
set_option maxHeartbeats 1000000

/-- Coefficient transport of actual homogeneous polynomials. -/
def mapForm (f : K →+* L) (p : Forms K n d) : Forms L n d :=
  ⟨MvPolynomial.map f p.val,p.property.map f⟩

@[simp] theorem mapForm_coordinates (f : K →+* L) (p : Forms K n d) (s : Sym (Fin n) d) :
    (formsBasis L n d).equivFun (mapForm f p) s =
      f ((formsBasis K n d).equivFun p s) := by
  simp only [TraceTranspose.formsBasis_equivFun_coeff,mapForm,coeff_map]

/-- Coordinate-defined actual quadrics commute with every field homomorphism. -/
theorem coefficientQuadrics_map (f : K →+* L) (a : CoefficientIndex n r → K) (i : Fin r) :
    mapForm f (coefficientQuadrics K n r a i) =
      coefficientQuadrics L n r (fun j => f (a j)) i := by
  apply (formsBasis L n 2).equivFun.injective
  funext s
  rw [mapForm_coordinates]
  simp only [coefficientQuadrics,LinearEquiv.apply_symm_apply]

/-- A multiplier basis vector is the actual quadratic family of the corresponding coordinate unit. -/
theorem multiplierBasis_apply (j : CoefficientIndex n r) :
    multiplierBasis (K := K) j = coefficientQuadrics K n r (Pi.single j 1) := by
  apply multiplierCoordinates.injective
  change (multiplierBasis (K := K)).equivFun (multiplierBasis j) = _
  funext i
  rw [Basis.equivFun_self]
  change (if j = i then 1 else 0) = (formsBasis K n 2).equivFun
    ((formsBasis K n 2).equivFun.symm (fun b => (Pi.single j (1 : K) : CoefficientIndex n r → K) (i.1,b))) i.2
  simp only [LinearEquiv.apply_symm_apply,Pi.single_apply]
  split_ifs <;> simp_all

/-- The genuine monomial multiplier vectors also commute with coefficient transport. -/
theorem multiplierBasis_map (f : K →+* L) (j : CoefficientIndex n r) (i : Fin r) :
    mapForm f (multiplierBasis (K := K) j i) = multiplierBasis (K := L) j i := by
  classical
  rw [multiplierBasis_apply,multiplierBasis_apply,coefficientQuadrics_map]
  congr 2
  funext x
  simp [Pi.single_apply]

/-- Actual multiplication commutes with transport of every polynomial coefficient. -/
theorem quadraticMultiplication_map (f : K →+* L) (q a : Fin r → Forms K n 2) :
    mapForm f (quadraticMultiplication q a) =
      quadraticMultiplication (fun i => mapForm f (q i)) (fun i => mapForm f (a i)) := by
  apply Subtype.ext
  simp only [mapForm,quadraticMultiplication_val,map_sum,map_mul]

/-- The coordinate multiplication matrix respects coefficient transport entry by entry. -/
theorem multiplicationMatrix_map (f : K →+* L) (a : CoefficientIndex n r → K) :
    (multiplicationMatrixLinear a).map f =
      multiplicationMatrixLinear (fun j => f (a j)) := by
  funext row col
  change f (LinearMap.toMatrix (multiplierBasis (K := K)) (formsBasis K n 4)
    (quadraticMultiplication (coefficientQuadrics K n r a)) row col) =
      LinearMap.toMatrix (multiplierBasis (K := L)) (formsBasis L n 4)
        (quadraticMultiplication (coefficientQuadrics L n r (fun j => f (a j)))) row col
  rw [LinearMap.toMatrix_apply,LinearMap.toMatrix_apply]
  rw [← Basis.equivFun_apply,← Basis.equivFun_apply,← mapForm_coordinates,
    quadraticMultiplication_map]
  have hq : (fun i => mapForm f (coefficientQuadrics K n r a i)) =
      coefficientQuadrics L n r (fun j => f (a j)) := funext (coefficientQuadrics_map f a)
  have ha : (fun i => mapForm f (multiplierBasis (K := K) col i)) =
      multiplierBasis (K := L) col := funext (multiplierBasis_map f col)
  rw [hq,ha]

/-- The symbolic matrix is defined over the base field, with the actual specialized map checked. -/
theorem genericMultiplicationMatrix_map (f : K →+* L) :
    (genericMultiplicationMatrix (K := K) (n := n) (r := r)).map (MvPolynomial.map f) =
      genericMultiplicationMatrix (K := L) := by
  classical
  funext row col
  change MvPolynomial.map f (polynomialOfLinear (multiplicationEntryLinear row col)) =
    polynomialOfLinear (multiplicationEntryLinear row col)
  simp only [polynomialOfLinear,map_sum,map_mul,map_C,map_X]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  have h := congrFun (congrFun (multiplicationMatrix_map f (Pi.single i 1)) row) col
  have he : (fun j => f ((Pi.single i (1 : K) : CoefficientIndex n r → K) j)) =
      (Pi.single i (1 : L) : CoefficientIndex n r → L) := by
    funext j
    simp [Pi.single_apply]
  rw [he] at h
  exact h


/-- Coefficient minors are unchanged apart from applying the coefficient homomorphism. -/
theorem coefficientMinor_map (f : K →+* L) (selected : Fin r → Sym (Fin n) 2) :
    MvPolynomial.map f (coefficientMinor (K := K) selected) = coefficientMinor (K := L) selected := by
  unfold coefficientMinor
  rw [(MvPolynomial.map f).map_det]
  congr 1
  funext i j
  simp

/-- Multiplication minors have the checked same compatibility as their actual matrices. -/
theorem multiplicationMinor_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : K →+* L) (rows : ι → Sym (Fin n) 4) (cols : ι → CoefficientIndex n r) :
    MvPolynomial.map f (multiplicationMinor (K := K) rows cols) =
      multiplicationMinor (K := L) rows cols := by
  unfold multiplicationMinor
  rw [(MvPolynomial.map f).map_det]
  change (((genericMultiplicationMatrix (K := K)).map (MvPolynomial.map f)).submatrix rows cols).det = _
  rw [genericMultiplicationMatrix_map]

/-- Any rank lower bound on a finite matrix has a minor of that size, independently of its index types. -/
theorem exists_minor {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β K) (t : ℕ) (ht : t ≤ A.rank) :
    ∃ rows : Fin t → α, ∃ cols : Fin t → β, (A.submatrix rows cols).det ≠ 0 := by
  classical
  let eα := Fintype.equivFin α
  let eβ := Fintype.equivFin β
  have hr : t ≤ (A.submatrix eα.symm eβ.symm).rank := by
    rw [Matrix.rank_submatrix]
    exact ht
  obtain ⟨u,v,hminor⟩ := KernelCharts.exists_minor_of_rank_le _ hr
  exact ⟨fun i => eα.symm (u i),fun i => eβ.symm (v i),hminor⟩

/-- Independence of actual quadrics supplies a nonzero coefficient minor with base-independent indices. -/
theorem exists_coefficient_minor (a : CoefficientIndex n r → K)
    (ha : LinearIndependent K (coefficientQuadrics K n r a)) :
    ∃ selected : Fin r → Sym (Fin n) 2,
      (Matrix.of (fun i j => a (i,selected j))).det ≠ 0 := by
  classical
  let e := Fintype.equivFin (Sym (Fin n) 2)
  let A : Matrix (Fin (Fintype.card (Sym (Fin n) 2))) (Fin r) K :=
    fun j i => a (i,e.symm j)
  have hc : LinearIndependent K (fun i => (formsBasis K n 2).equivFun (coefficientQuadrics K n r a i)) :=
    ha.map' (formsBasis K n 2).equivFun.toLinearMap (LinearMap.ker_eq_bot.mpr (formsBasis K n 2).equivFun.injective)
  have hA : LinearIndependent K (fun i => A.col i) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft K K e)
    have he : (LinearMap.funLeft K K e) ∘ (fun i => A.col i) =
        (fun i => (formsBasis K n 2).equivFun (coefficientQuadrics K n r a i)) := by
      funext i b
      change a (i,e.symm (e b)) = (formsBasis K n 2).equivFun
        ((formsBasis K n 2).equivFun.symm (fun s => a (i,s))) b
      rw [e.symm_apply_apply,LinearEquiv.apply_symm_apply]
    rw [he]
    exact hc
  obtain ⟨u,hu⟩ := KernelCharts.exists_rows_for_independent_columns A
    (Function.Embedding.refl (Fin r)) hA
  refine ⟨fun j => e.symm (u j),?_⟩
  change (KernelCharts.minor A u (Function.Embedding.refl (Fin r))).transpose.det ≠ 0
  rwa [Matrix.det_transpose]

/-- Generic quartic maximal rank descends along any field homomorphism to an infinite base field.
The minors are of the literal coefficient and multiplication matrices; no scalar-extension rank
hypothesis or algebraicity assumption is required. -/
theorem genericQuartic_descend [Infinite K] (f : K →+* L) (hGeneric : GenericQuartic L n r) :
    GenericQuartic K n r := by
  classical
  obtain ⟨D,⟨aL,hDa⟩,hgood⟩ := hGeneric
  obtain ⟨hlin,hquot⟩ := hgood aL hDa
  have hlinForms : LinearIndependent L (coefficientQuadrics L n r aL) :=
    LinearIndependent.of_comp (Forms L n 2).subtype hlin
  obtain ⟨selected,hcoeff⟩ := exists_coefficient_minor aL hlinForms
  let t := (multiplicationMatrixLinear aL).rank
  obtain ⟨rows,cols,hmult⟩ := exists_minor (multiplicationMatrixLinear aL) t le_rfl
  have hsize : (n+3).choose 4 ≤ Fintype.card (Fin t) + expectedDimension n r := by
    have hdim := quartic_quotient_add_rank (coefficientQuadrics L n r aL)
    change finrank L (QuarticQuotient L n (coefficientSpace L n r aL)) +
      finrank L (quadraticMultiplication (coefficientQuadrics L n r aL)).range = (n+3).choose 4 at hdim
    rw [hquot,← multiplicationMatrix_rank] at hdim
    simp only [Fintype.card_fin]
    dsimp [t]
    omega
  have hcL : eval aL (MvPolynomial.map f (coefficientMinor (K := K) selected)) ≠ 0 := by
    rw [coefficientMinor_map,eval_coefficientMinor]
    exact hcoeff
  have hmL : eval aL (MvPolynomial.map f (multiplicationMinor (K := K) rows cols)) ≠ 0 := by
    rw [multiplicationMinor_map,eval_multiplicationMinor]
    exact hmult
  have hcK : coefficientMinor (K := K) selected ≠ 0 := by
    intro hz
    simp only [hz,map_zero] at hcL
    exact hcL rfl
  have hmK : multiplicationMinor (K := K) rows cols ≠ 0 := by
    intro hz
    simp only [hz,map_zero] at hmL
    exact hmL rfl
  obtain ⟨aK,haK⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hcK hmK)
  have hparts : eval aK (coefficientMinor selected) ≠ 0 ∧ eval aK (multiplicationMinor rows cols) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    simpa only [map_mul] using haK
  apply genericQuartic_of_nonzero_minors selected rows cols aK
  · simpa only [eval_coefficientMinor] using hparts.1
  · simpa only [eval_multiplicationMinor] using hparts.2
  · exact hsize

/-- The whole generic statement descends along a field homomorphism. -/
theorem mainGeneric_descend [Infinite K] (f : K →+* L) (h : MainGenericStatement L) :
    MainGenericStatement K := by
  intro n hn r hr
  exact genericQuartic_descend f (h n hn r hr)

/-- Convenient algebra-extension form; no algebraicity hypothesis is needed. -/
theorem genericQuartic_descend_algebra [Infinite K] [Algebra K L]
    (h : GenericQuartic L n r) : GenericQuartic K n r :=
  genericQuartic_descend (algebraMap K L) h

end Quartic.GenericFieldDescent
