module

public import Froberg.Graded
public import Froberg.GeneralPositionVectors
public import Froberg.MonomialIncidence

@[expose] public section

/-! Actual polynomial multiplication by monomial-attached vector generators. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {n s d : ℕ}

/-- Attach a vector to each prescribed monomial and multiply it by a homogeneous
coefficient polynomial. Outputs are genuine tuples of multivariate polynomials. -/
def multiplication (e : I → Fin n →₀ ℕ) (v : I → J → K) :
    (I → Forms K n d) →ₗ[K] (J → Poly K n) where
  toFun a j := ∑ i, monomial (e i) (v i j) * (a i).val
  map_add' a b := by
    ext j
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext j
    simp only [Pi.smul_apply, Submodule.coe_smul, mul_smul_comm, Finset.smul_sum,
      RingHom.id_apply]

@[simp] theorem multiplication_apply (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (a : I → Forms K n d) (j : J) :
    multiplication e v a j = ∑ i, monomial (e i) (v i j) * (a i).val := rfl

/-- The target coefficient lies in the span of the vectors attached to its divisors. -/
theorem coefficient_formula (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (a : I → Forms K n d) (β : Fin n →₀ ℕ) (j : J) :
    (multiplication e v a j).coeff β =
      ∑ i : {i // e i ≤ β}, (a i.val).val.coeff (β-e i.val) * v i.val j := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => e i ≤ β))
    (by simp) (fun i => (a i).val.coeff (β-e i) * v i j)]
  simp only [multiplication_apply,MvPolynomial.coeff_sum,coeff_monomial_mul',
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_comm]

/-- Independence in each actual target fiber proves polynomial injectivity in
the requested degree. Only degree-(s+d) target fibers are needed. -/
theorem injective_of_independent_fibers (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s)
    (hv : ∀ β : Fin n →₀ ℕ, β.degree = s+d →
      LinearIndependent K (fun i : {i // e i ≤ β} => v i.val)) :
    Function.Injective (multiplication (d := d) e v) := by
  classical
  have hker : ∀ a : I → Forms K n d, multiplication e v a = 0 → a = 0 := by
    intro a ha
    funext i
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    by_cases hm : m.degree = d
    · let β := e i + m
      have hb : β.degree = s+d := by simp only [β,map_add,he,hm]
      have hf : ∑ z : {i // e i ≤ β}, (a z.val).val.coeff (β-e z.val) • v z.val = 0 := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← coefficient_formula]
        rw [ha]
        simp
      have hi : e i ≤ β := le_add_right le_rfl
      have hz := Fintype.linearIndependent_iff.mp (hv β hb)
        (fun z => (a z.val).val.coeff (β-e z.val)) hf ⟨i,hi⟩
      simpa [β,add_tsub_cancel_left] using hz
    · simpa using (a i).property.coeff_eq_zero hm
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub,hab,sub_self]

/-- Every output has the expected total degree. -/
theorem multiplication_homogeneous (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (a : I → Forms K n d) (j : J) :
    (multiplication e v a j).IsHomogeneous (s+d) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact (MvPolynomial.isHomogeneous_monomial (v i j) (he i)).mul (a i).property

/-- The same multiplication, retained inside its actual homogeneous target. -/
def homogeneousMultiplication (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) :
    (I → Forms K n d) →ₗ[K] (J → Forms K n (s+d)) :=
  LinearMap.pi (fun j => (((LinearMap.proj j).comp (multiplication e v)).codRestrict
    (Forms K n (s+d)) (fun a => multiplication_homogeneous e v he a j)))

@[simp] theorem homogeneousMultiplication_val (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (a : I → Forms K n d) (j : J) :
    (homogeneousMultiplication e v he a j).val = multiplication e v a j := rfl

/-- The degree-specific relations defining the outer quotient. -/
def relationSpace (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i, (e i).degree = s) :
    Submodule K (J → Forms K n (s+d)) := LinearMap.range (homogeneousMultiplication e v he)

theorem homogeneousMultiplication_injective (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (hv : Function.Injective (multiplication (d := d) e v)) :
    Function.Injective (homogeneousMultiplication (d := d) e v he) := by
  intro a b hab
  apply hv
  funext j
  exact congrArg Subtype.val (congrFun hab j)

/-- Exact quotient dimensions follow from the proved polynomial injection. -/
theorem quotient_finrank_of_injective (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (hn : 0 < n)
    (hv : Function.Injective (multiplication (d := d) e v)) :
    Module.finrank K ((J → Forms K n (s+d)) ⧸ relationSpace (d := d) e v he) =
      Fintype.card J * (n+(s+d)-1).choose (s+d) -
        Fintype.card I * (n+d-1).choose d := by
  have hi := homogeneousMultiplication_injective e v he hv
  have hd := (relationSpace (d := d) e v he).finrank_quotient_add_finrank
  have hr : Module.finrank K (relationSpace (d := d) e v he) =
      Module.finrank K (I → Forms K n d) := LinearMap.finrank_range_of_inj hi
  rw [hr] at hd
  have hc := Nat.eq_sub_of_add_eq hd
  simpa only [Module.finrank_pi_fintype,finrank_forms K n (s+d) hn,
    finrank_forms K n d hn,Finset.sum_const,Finset.card_univ,smul_eq_mul] using hc

end Froberg.AttachedMultiplication
