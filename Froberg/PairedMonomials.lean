module

public import Froberg.ProductFibers
public import Froberg.ProductMinors
public import Froberg.Graded
public import Mathlib.Data.Finsupp.Indicator

@[expose] public section

/-! Concrete paired-variable monomials and their index-degree product fibers. -/
noncomputable section
namespace Froberg.PairedMonomials
open Finset MvPolynomial
variable {X : Type*} [DecidableEq X]

/-- Exponents of x_A y_(S∖A), with `true` marking x and `false` marking y. -/
def pairedExponent (S A : Finset X) : (X × Bool) →₀ ℕ :=
  Finsupp.indicator (S.product Finset.univ) (fun z _ =>
    if z.2 then (if z.1 ∈ A then 1 else 0) else (if z.1 ∈ A then 0 else 1))

@[simp] theorem pairedExponent_true (S A : Finset X) (x : X) :
    pairedExponent S A (x,true) = if x ∈ S ∩ A then 1 else 0 := by
  by_cases hs : x ∈ S <;> by_cases ha : x ∈ A <;> simp [pairedExponent,hs,ha]

@[simp] theorem pairedExponent_false (S A : Finset X) (x : X) :
    pairedExponent S A (x,false) = if x ∈ S \ A then 1 else 0 := by
  by_cases hs : x ∈ S <;> by_cases ha : x ∈ A <;> simp [pairedExponent,hs,ha]

/-- The multidegree which gives x_i and y_i the same degree. -/
def indexDegree (e : (X × Bool) →₀ ℕ) : X → ℕ := fun x => e (x,true) + e (x,false)

omit [DecidableEq X] in
@[simp] theorem indexDegree_add (e f : (X × Bool) →₀ ℕ) :
    indexDegree (e + f) = indexDegree e + indexDegree f := by
  ext x
  simp [indexDegree, add_comm, add_left_comm]

@[simp] theorem indexDegree_pairedExponent (S A : Finset X) :
    indexDegree (pairedExponent S A) = fun x => if x ∈ S then 1 else 0 := by
  ext x
  simp only [indexDegree, pairedExponent_true, pairedExponent_false,
    Finset.mem_inter, Finset.mem_sdiff]
  split_ifs <;> simp_all

@[simp] theorem degree_pairedExponent [Fintype X] (S A : Finset X) :
    (pairedExponent S A).degree = S.card := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  have he (x : X) : (∑ b : Bool, pairedExponent S A (x,b)) = if x ∈ S then 1 else 0 := by
    simpa only [Fintype.sum_bool, indexDegree, add_comm] using congrFun (indexDegree_pairedExponent S A) x
  simp_rw [he]
  simp

/-- Equality of product index degrees is exactly equality of the doubled and
single-or-doubled index sets. -/
theorem product_indexDegree_eq_iff (S T U V A B C D : Finset X) :
    indexDegree (pairedExponent S A + pairedExponent T B) =
      indexDegree (pairedExponent U C + pairedExponent V D) ↔
    S ∩ T = U ∩ V ∧ S ∪ T = U ∪ V := by
  simp only [indexDegree_add, indexDegree_pairedExponent]
  constructor
  · intro h
    constructor <;> ext x
    all_goals
      have hx := congrFun h x
      simp only [Pi.add_apply] at hx
      simp only [Finset.mem_inter, Finset.mem_union]
      by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
        by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;> simp_all
  · rintro ⟨hi, hu⟩
    ext x
    have hi' := Finset.ext_iff.mp hi x
    have hu' := Finset.ext_iff.mp hu x
    simp only [Finset.mem_inter, Finset.mem_union] at hi' hu'
    simp only [Pi.add_apply]
    by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
      by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;> simp_all

/-- A target has xy on J, y² on I∖J, and x_D y_(R∖D) on the single indices. -/
def targetExponent (I J R D : Finset X) : (X × Bool) →₀ ℕ :=
  pairedExponent I J + pairedExponent I ∅ + pairedExponent R D

/-- Distinct target subsets give distinct actual monomials. -/
theorem targetExponent_inj {I J R D E : Finset X} (hIR : Disjoint I R)
    (hD : D ⊆ R) (hE : E ⊆ R) (h : targetExponent I J R D = targetExponent I J R E) :
    D = E := by
  ext x
  by_cases hx : x ∈ R
  · have hi : x ∉ I := fun hi => Finset.disjoint_left.mp hIR hi hx
    have he := DFunLike.congr_fun h (x,true)
    simp only [targetExponent, Finsupp.add_apply, pairedExponent_true,
      Finset.mem_inter, hi, false_and, reduceIte, zero_add] at he
    by_cases hd : x ∈ D <;> by_cases he' : x ∈ E <;> simp_all
  · have hd : x ∉ D := fun h => hx (hD h)
    have he : x ∉ E := fun h => hx (hE h)
    simp [hd,he]

/-- The explicit allowed factors of a matched target monomial. -/
theorem paired_factorization {I J P Q D E : Finset X}
    (hIP : Disjoint I P) (hIQ : Disjoint I Q) (hPQ : Disjoint P Q)
    (hJI : J ⊆ I) (hEJ : E ⊆ J) (hD : D ⊆ P ∪ Q) :
    pairedExponent (I ∪ P) (E ∪ (D ∩ P)) +
      pairedExponent (I ∪ Q) ((J \ E) ∪ (D ∩ Q)) =
    targetExponent I J (P ∪ Q) D := by
  ext ⟨x,b⟩
  have hip := Finset.disjoint_left.mp hIP
  have hiq := Finset.disjoint_left.mp hIQ
  have hpq := Finset.disjoint_left.mp hPQ
  have hji := fun h : x ∈ J => hJI h
  have hej := fun h : x ∈ E => hEJ h
  have hd := fun h : x ∈ D => Finset.mem_union.mp (hD h)
  cases b <;>
    simp only [targetExponent, Finsupp.add_apply, pairedExponent_true, pairedExponent_false,
      Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, not_false_eq_true,
      and_true] <;>
    by_cases hi : x ∈ I <;> by_cases hp : x ∈ P <;> by_cases hq : x ∈ Q <;>
    by_cases hj : x ∈ J <;> by_cases he : x ∈ E <;> by_cases hd' : x ∈ D <;> simp_all

/-- The permitted exponents of one form of x-degree a on support S. -/
def allowedExponents (a : ℕ) (S : Finset X) : Finset ((X × Bool) →₀ ℕ) :=
  (S.powersetCard a).image (pairedExponent S)

theorem mem_allowedExponents {a : ℕ} {S A : Finset X} (hA : A ⊆ S) (ha : A.card = a) :
    pairedExponent S A ∈ allowedExponents a S := by
  exact Finset.mem_image.mpr ⟨A, Finset.mem_powersetCard.mpr ⟨hA,ha⟩, rfl⟩

end Froberg.PairedMonomials
