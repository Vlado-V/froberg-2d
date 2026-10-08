import Quartic.FiniteEndpointChecker
import Quartic.MinorLift
import Quartic.EndpointReduction
import Mathlib.Data.List.Sort

/-! Field-independent sparse monomial certificates for actual polynomial families. -/
namespace Quartic.FiniteEndpointCheckerPolynomial
open Matrix Module MvPolynomial
open Quartic.FiniteEndpointChecker
set_option maxHeartbeats 1000000

/-- Integral lift keeps repeated sparse entries, so no distinctness assumption is hidden. -/
def integerMatrix {n : ℕ} (A : Fin n → List (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of (fun i => ((A i).map (fun j => Pi.single j (1 : ℤ))).sum)

theorem sparse_cast {n : ℕ} {K : Type*} [CommRing K] (s : List (Fin n)) :
    (fun j => (((s.map (fun i => Pi.single i (1 : ℤ))).sum j : ℤ) : K)) =
      (s.map (fun i => Pi.single i (1 : K))).sum := by
  classical
  induction s with
  | nil => ext j; simp
  | cons i s ih =>
    ext j
    simp only [List.map_cons,List.sum_cons,Pi.add_apply,Int.cast_add]
    rw [congrFun ih j]
    simp [Pi.single_apply]

theorem integerMatrix_binary {n : ℕ} (A : Fin n → List (Fin n)) :
    (integerMatrix A).map (Int.castRingHom (ZMod 2)) = sparseMatrix A := by
  ext i j
  exact congrFun (sparse_cast (K := ZMod 2) (A i)) j

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {n v : ℕ}

theorem integral_rows_independent (A : Fin n → List (Fin n)) (B : Fin n → ℕ)
    (h : checkInverse A B = true) :
    LinearIndependent K (fun i => (((A i).map (fun j => Pi.single j (1 : K))).sum)) := by
  have hd : (((integerMatrix A).map (Int.castRingHom K))).det ≠ 0 :=
    MinorLift.charZero_det_ne_zero_of_binary (integerMatrix A) (by
      rw [integerMatrix_binary]
      exact determinant_ne_zero A B h)
  have hi := Matrix.linearIndependent_rows_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have he : ((integerMatrix A).map (Int.castRingHom K)).row =
      fun i => ((A i).map (fun j => Pi.single j (1 : K))).sum := by
    funext i
    exact sparse_cast (A i)
  rwa [he] at hi

/-- Actual sparse sums of monomials, over any characteristic-zero field. -/
def rowPolynomial (E : Fin n → Fin v →₀ ℕ) (s : List (Fin n)) : Poly K v :=
  (s.map (fun j => monomial (E j) (1 : K))).sum

theorem coefficients_rowPolynomial (E : Fin n → Fin v →₀ ℕ) (hE : Function.Injective E)
    (s : List (Fin n)) :
    (fun j => (rowPolynomial (K := K) E s).coeff (E j)) =
      (s.map (fun i => Pi.single i (1 : K))).sum := by
  classical
  induction s with
  | nil => ext j; simp [rowPolynomial]
  | cons i s ih =>
    ext j
    simp only [rowPolynomial,List.map_cons,List.sum_cons,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_monomial,Pi.add_apply]
    simp only [hE.eq_iff]
    have hij := congrFun ih j
    change ((s.map (fun i => monomial (E i) (1 : K))).sum).coeff (E j) = _ at hij
    rw [hij]
    simp [Pi.single_apply,eq_comm]

/-- A checked binary inverse establishes independence of actual characteristic-zero
polynomials, via the integral minor and literal coefficient functionals. -/
theorem rowPolynomials_independent (E : Fin n → Fin v →₀ ℕ) (hE : Function.Injective E)
    (A : Fin n → List (Fin n)) (B : Fin n → ℕ) (h : checkInverse A B = true) :
    LinearIndependent K (fun i => rowPolynomial (K := K) E (A i)) := by
  let C : Poly K v →ₗ[K] (Fin n → K) := LinearMap.pi (fun j => MvPolynomial.lcoeff K (E j))
  apply LinearIndependent.of_comp C
  change LinearIndependent K (fun i j => (rowPolynomial (K := K) E (A i)).coeff (E j))
  have he : (fun i j => (rowPolynomial (K := K) E (A i)).coeff (E j)) =
      (fun i => ((A i).map (fun j => Pi.single j (1 : K))).sum) :=
    funext (fun i => coefficients_rowPolynomial E hE (A i))
  rw [he]
  exact integral_rows_independent A B h

/-- An explicit variable list represents its exponent multiset. -/
def listExponent (xs : List (Fin v)) : Fin v →₀ ℕ :=
  Multiset.toFinsupp (xs : Multiset (Fin v))

theorem listExponent_degree (xs : List (Fin v)) : (listExponent xs).degree = xs.length := by
  exact Multiset.toFinsupp_sum_eq (xs : Multiset (Fin v))

theorem listExponent_append (xs ys : List (Fin v)) :
    listExponent (xs ++ ys) = listExponent xs + listExponent ys := by
  exact Multiset.toFinsupp_add (xs : Multiset (Fin v)) (ys : Multiset (Fin v))

theorem listExponent_sort (xs : List (Fin v)) :
    listExponent (xs.insertionSort (· ≤ ·)) = listExponent xs := by
  apply congrArg Multiset.toFinsupp
  exact Multiset.coe_eq_coe.mpr (List.perm_insertionSort (· ≤ ·) _)

/-- A cheap candidate decoder for lexicographically ordered nondecreasing variable lists.
Only its checked left-inverse equations are used; no enumeration correctness is assumed. -/
def tupleRank (v lo : ℕ) : List (Fin v) → ℕ
  | [] => 0
  | x :: xs => (v - lo + xs.length).choose (xs.length + 1) -
      (v - x.val + xs.length).choose (xs.length + 1) + tupleRank v x.val xs

theorem injective_of_tupleRank {b : ℕ} (V : Fin b → List (Fin v))
    (h : ∀ i, tupleRank v 0 (V i) = i.val) : Function.Injective V := by
  intro i j he
  apply Fin.ext
  calc
    i.val = tupleRank v 0 (V i) := (h i).symm
    _ = tupleRank v 0 (V j) := congrArg (tupleRank v 0) he
    _ = j.val := h j

theorem listExponent_injective_of_sorted {b : ℕ} (V : Fin b → List (Fin v))
    (hV : Function.Injective V) (hs : ∀ i, (V i).Pairwise (· ≤ ·)) :
    Function.Injective (fun i => listExponent (V i)) := by
  intro i j h
  apply hV
  apply List.Perm.eq_of_pairwise' (hs i) (hs j)
  apply Multiset.coe_eq_coe.mp
  exact Multiset.toFinsupp.injective h

theorem support_identity_of_lists {b : ℕ} (V : Fin n → List (Fin v))
    (Q : Fin b → List (Fin v)) (e : List (Fin v)) (A : List (Fin n))
    (s : List (Fin b))
    (h : A.map V = s.map (fun j => (Q j ++ e).insertionSort (· ≤ ·))) :
    A.map (fun i => listExponent (V i)) =
      s.map (fun j => listExponent (Q j) + listExponent e) := by
  have hh := congrArg (List.map (listExponent (v := v))) h
  simpa only [List.map_map,Function.comp_def,listExponent_sort,listExponent_append] using hh

theorem rowPolynomial_mul_monomial (E : Fin n → Fin v →₀ ℕ) (s : List (Fin n))
    (e : Fin v →₀ ℕ) :
    rowPolynomial (K := K) E s * monomial e 1 =
      (s.map (fun j => monomial (E j + e) (1 : K))).sum := by
  induction s with
  | nil => simp [rowPolynomial]
  | cons i s ih =>
    simp only [rowPolynomial,List.map_cons,List.sum_cons,add_mul,monomial_mul_monomial,one_mul]
    exact congrArg (fun z => monomial (E i + e) (1 : K) + z) ih

/-- A finite list-of-exponents equality certifies the product-polynomial identity.
This separates cheap combinatorial data checking from all field reasoning. -/
theorem product_identity (E : Fin n → Fin v →₀ ℕ) {b : ℕ}
    (Q : Fin b → Fin v →₀ ℕ) (s : List (Fin b)) (e : Fin v →₀ ℕ)
    (A : List (Fin n))
    (h : A.map E = s.map (fun j => Q j + e)) :
    rowPolynomial (K := K) Q s * monomial e 1 = rowPolynomial E A := by
  rw [rowPolynomial_mul_monomial]
  have hh := congrArg (fun xs => (xs.map (fun z => monomial z (1 : K))).sum) h
  simpa only [List.map_map,Function.comp_def,rowPolynomial] using hh.symm

/-- Coefficient minors can also certify families with terms outside that minor. -/
theorem polynomials_independent_of_coefficients
    (p : Fin n → Poly K v) (E : Fin n → Fin v →₀ ℕ)
    (A : Fin n → List (Fin n)) (B : Fin n → ℕ) (h : checkInverse A B = true)
    (hcoeff : ∀ i, (fun j => (p i).coeff (E j)) =
      ((A i).map (fun j => Pi.single j (1 : K))).sum) : LinearIndependent K p := by
  let C : Poly K v →ₗ[K] (Fin n → K) := LinearMap.pi (fun j => MvPolynomial.lcoeff K (E j))
  apply LinearIndependent.of_comp C
  change LinearIndependent K (fun i j => (p i).coeff (E j))
  rw [show (fun i j => (p i).coeff (E j)) =
      (fun i => ((A i).map (fun j => Pi.single j (1 : K))).sum) from funext hcoeff]
  exact integral_rows_independent A B h

theorem sparse_count (s : List (Fin n)) (j : Fin n) :
    (s.map (fun i => Pi.single i (1 : K))).sum j = (s.count j : K) := by
  classical
  induction s with
  | nil => simp
  | cons i s ih =>
    simp only [List.map_cons,List.sum_cons,Pi.add_apply]
    rw [ih]
    by_cases h : i = j
    · subst i
      simp only [Pi.single_eq_same,List.count_cons_self,Nat.cast_add,Nat.cast_one]
      exact add_comm _ _
    · rw [List.count_cons_of_ne h]
      simp [Pi.single_apply,h,Ne.symm h]

theorem rowPolynomial_coeff_count (E : Fin n → Fin v →₀ ℕ) (hE : Function.Injective E)
    (s : List (Fin n)) (j : Fin n) :
    (rowPolynomial (K := K) E s).coeff (E j) = (s.count j : K) := by
  rw [congrFun (coefficients_rowPolynomial E hE s) j,sparse_count]

/-- Sparse sums are homogeneous from their individual listed exponents. -/
def rowForm {d : ℕ} (E : Fin n → Fin v →₀ ℕ) (hE : ∀ i, (E i).degree = d)
    (s : List (Fin n)) : Forms K v d :=
  ⟨rowPolynomial E s, by
    induction s with
    | nil => exact isHomogeneous_zero (Fin v) K _
    | cons i s ih =>
      exact (isHomogeneous_monomial (1 : K) (hE i)).add ih⟩

theorem rowForms_independent {d : ℕ} (E : Fin n → Fin v →₀ ℕ)
    (hdeg : ∀ i, (E i).degree = d) (hE : Function.Injective E)
    (A : Fin n → List (Fin n)) (B : Fin n → ℕ) (h : checkInverse A B = true) :
    LinearIndependent K (fun i => rowForm (K := K) E hdeg (A i)) :=
  LinearIndependent.of_comp (Forms K v d).subtype (rowPolynomials_independent E hE A B h)

theorem product_mem_range {r : ℕ} (q : Fin r → Forms K v 2) (i : Fin r)
    (a : Forms K v 2) : mulQuadratic (q i) a ∈ LinearMap.range (quadraticMultiplication q) := by
  classical
  refine ⟨Pi.single i a, ?_⟩
  apply Subtype.ext
  simp only [quadraticMultiplication_val,mulQuadratic,Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem rank_lower_bound {r s : ℕ} (q : Fin r → Forms K v 2)
    (f : Fin s → Forms K v 4) (hf : LinearIndependent K f)
    (hmem : ∀ i, f i ∈ LinearMap.range (quadraticMultiplication q)) :
    s ≤ finrank K (LinearMap.range (quadraticMultiplication q)) := by
  have hs : Submodule.span K (Set.range f) ≤ LinearMap.range (quadraticMultiplication q) :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hmem i)
  simpa [finrank_span_eq_card hf] using Submodule.finrank_mono hs

end
end Quartic.FiniteEndpointCheckerPolynomial
