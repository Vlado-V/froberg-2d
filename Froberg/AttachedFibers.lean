module

public import Froberg.AttachedMultiplication
public import Quartic.HomogeneousCoefficientCoordinates
public import Mathlib.LinearAlgebra.Quotient.Pi

@[expose] public section

/-! The actual outer quotient decomposes into its monomial vector fibers. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open MvPolynomial
open Quartic.HomogeneousCoefficientCoordinates
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {n s d : ℕ}

/-- Literal polynomial coefficients, regrouped by monomial rather than output row. -/
def rowCoordinates : (J → Forms K n d) ≃ₗ[K] (Exponent n d → J → K) where
  toFun p β j := (p j).val.coeff β.val
  invFun c j := equiv.symm (fun β => c β j)
  left_inv p := by funext j; exact equiv.symm_apply_apply (p j)
  right_inv c := by
    funext β j
    exact congrFun (equiv.apply_symm_apply (fun γ => c γ j)) β
  map_add' p q := by ext β j; simp
  map_smul' c p := by ext β j; simp

@[simp] theorem rowCoordinates_apply (p : J → Forms K n d) (β : Exponent n d) (j : J) :
    rowCoordinates p β j = (p j).val.coeff β.val := rfl

/-- The subspace killed in one monomial vector fiber. -/
def relationFiber (e : I → Fin n →₀ ℕ) (v : I → J → K) (β : Fin n →₀ ℕ) :
    Submodule K (J → K) := Submodule.span K (Set.range (fun i : {i // e i ≤ β} => v i.val))

private theorem multiplication_single [DecidableEq I] (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (i : I) (f : Forms K n d) (j : J) :
    multiplication e v (Pi.single i f) j = monomial (e i) (v i j) * f.val := by
  simp [multiplication,Pi.single_apply,apply_ite]

/-- Every single attached vector in a target monomial fiber is an actual relation. -/
theorem single_relationFiber_generator (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (β : Exponent n (s+d)) (i : I) (hi : e i ≤ β.val) :
    Pi.single β (v i) ∈ (relationSpace (d := d) e v he).map rowCoordinates.toLinearMap := by
  classical
  have heq : e i + (β.val-e i) = β.val := add_tsub_cancel_of_le hi
  have hdeg : (β.val-e i).degree = d := by
    have h := congrArg Finsupp.degree heq
    rw [map_add,he i,β.property] at h
    omega
  let f : Forms K n d := ⟨monomial (β.val-e i) 1,isHomogeneous_monomial 1 hdeg⟩
  let a : I → Forms K n d := Pi.single i f
  refine ⟨homogeneousMultiplication e v he a,⟨a,rfl⟩,?_⟩
  ext γ j
  change (multiplication e v a j).coeff γ.val =
    (Pi.single β (v i) : Exponent n (s+d) → J → K) γ j
  rw [show a = Pi.single i f from rfl,multiplication_single]
  change (monomial (e i) (v i j) * monomial (β.val-e i) 1).coeff γ.val = _
  rw [monomial_mul_monomial,mul_one,heq,coeff_monomial]
  by_cases hγ : γ = β
  · subst γ
    simp
  · have hval : β.val ≠ γ.val := fun h => hγ (Subtype.ext h.symm)
    simp [hγ,hval]

/-- The image of the polynomial relation space is exactly the product of its
monomial relation fibers. No genericity or vector independence is assumed. -/
theorem rowCoordinates_map_relations (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) :
    (relationSpace (d := d) e v he).map rowCoordinates.toLinearMap =
      Submodule.pi Set.univ (fun β : Exponent n (s+d) => relationFiber e v β.val) := by
  classical
  apply le_antisymm
  · rintro x ⟨y,⟨a,rfl⟩,rfl⟩
    apply Submodule.mem_pi.mpr
    intro β _
    have hcoeff : rowCoordinates (homogeneousMultiplication e v he a) β =
        ∑ i : {i // e i ≤ β.val}, (a i.val).val.coeff (β.val-e i.val) • v i.val := by
      funext j
      simpa only [rowCoordinates_apply,homogeneousMultiplication_val,
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using coefficient_formula e v a β.val j
    change rowCoordinates (homogeneousMultiplication e v he a) β ∈ relationFiber e v β.val
    rw [hcoeff]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · intro x hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro β _
    have hβ : x β ∈ relationFiber e v β.val := Submodule.mem_pi.mp hx β (Set.mem_univ β)
    generalize hy : x β = y at hβ ⊢
    clear hy
    induction hβ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      exact single_relationFiber_generator e v he β i.val i.property
    | zero => simp
    | add y z _ _ hy hz =>
      simpa only [Pi.single_add] using Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      simpa only [Pi.single_smul] using Submodule.smul_mem _ c hy

/-- Exact decomposition of the genuine polynomial quotient into vector-space
quotients, one for each target monomial. -/
def quotientFiberEquiv (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) :
    ((J → Forms K n (s+d)) ⧸ relationSpace (d := d) e v he) ≃ₗ[K]
      (∀ β : Exponent n (s+d), (J → K) ⧸ relationFiber e v β.val) :=
  (Submodule.Quotient.equiv _ _ rowCoordinates (rowCoordinates_map_relations e v he)).trans
    (Submodule.quotientPi _)

end Froberg.AttachedMultiplication
