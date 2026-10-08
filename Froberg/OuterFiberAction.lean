import Froberg.OuterMultiplication
import Froberg.AttachedProjection

/-! Monomial multiplication acts by the actual quotient projections on outer fibers. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open MvPolynomial Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s d h : ℕ}

@[simp] theorem quotientFiberEquiv_mk (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i, (e i).degree = s) (p : Fin h → Forms K n (s+d))
    (β : Exponent n (s+d)) :
    quotientFiberEquiv e v he ((relationSpace (d := d) e v he).mkQ p) β =
      (relationFiber e v β.val).mkQ (fun j => (p j).val.coeff β.val) := rfl

/-- A vector-valued monomial of a prescribed homogeneous degree. -/
def monomialVector (a : Exponent n s) (u : Fin h → K) : Fin h → Forms K n s :=
  fun j => ⟨monomial a.val (u j),isHomogeneous_monomial (u j) a.property⟩

theorem quotientFiberEquiv_symm_single_mk (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i, (e i).degree = s) (a : Exponent n s) (u : Fin h → K) :
    (quotientFiberEquiv (d := 0) e v he).symm
      (Pi.single a ((relationFiber e v a.val).mkQ u)) =
        (relationSpace (d := 0) e v he).mkQ (monomialVector a u) := by
  apply (quotientFiberEquiv (d := 0) e v he).injective
  rw [LinearEquiv.apply_symm_apply]
  funext b
  rw [quotientFiberEquiv_mk]
  by_cases hab : b=a
  · subst b
    simp [monomialVector]
  · have hval : a.val ≠ b.val := fun he => hab (Subtype.ext he.symm)
    simp [Pi.single_eq_of_ne hab,monomialVector,coeff_monomial,hval]
    exact (map_zero (relationFiber e v b.val).mkQ).symm

/-- The genuine multiplication conjugated by the proved coefficient-quotient equivalences. -/
def fiberMultiply (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i, (e i).degree = s) :
    Forms K n d →ₗ[K]
      ((a : Exponent n s) → (Fin h → K) ⧸ relationFiber e v a.val) →ₗ[K]
      ((b : Exponent n (s+d)) → (Fin h → K) ⧸ relationFiber e v b.val) where
  toFun f := (quotientFiberEquiv e v he).toLinearMap.comp
    ((quotientMultiply e v he f).comp (quotientFiberEquiv (d := 0) e v he).symm.toLinearMap)
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

/-- Adding a multiplier exponent to the source exponent. -/
abbrev addExponent (a : Exponent n s) (b : Exponent n d) : Exponent n (s+d) :=
  ⟨a.val+b.val,by simp [a.property,b.property]⟩

/-- The homogeneous monomial with coefficient one. -/
def monomialForm (b : Exponent n d) : Forms K n d :=
  ⟨monomial b.val 1,isHomogeneous_monomial 1 b.property⟩

/-- In a single source fiber, multiplying by one monomial has precisely one
nonzero target fiber, where it is the canonical quotient projection. -/
theorem fiberMultiply_monomial_single (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i, (e i).degree = s) (a : Exponent n s) (b : Exponent n d)
    (u : (Fin h → K) ⧸ relationFiber e v a.val) :
    fiberMultiply e v he (monomialForm b) (Pi.single a u) =
      Pi.single (addExponent a b) (fiberProjection e v (le_add_right le_rfl) u) := by
  obtain ⟨u,rfl⟩ := (relationFiber e v a.val).mkQ_surjective u
  change quotientFiberEquiv e v he
    (quotientMultiply e v he (monomialForm b)
      ((quotientFiberEquiv (d := 0) e v he).symm (Pi.single a _))) = _
  rw [quotientFiberEquiv_symm_single_mk,quotientMultiply_mk]
  funext c
  rw [quotientFiberEquiv_mk]
  by_cases hca : c=addExponent a b
  · subst c
    simp [monomialVector,monomialForm,vectorMultiply_val,monomial_mul_monomial,
      addExponent,add_comm,fiberProjection]
  · have hval : b.val+a.val ≠ c.val := by
      intro hh
      apply hca
      apply Subtype.ext
      simpa [addExponent,add_comm] using hh.symm
    rw [Pi.single_eq_of_ne hca]
    simp [monomialVector,monomialForm,vectorMultiply_val,
      monomial_mul_monomial,coeff_monomial,hval]
    exact (relationFiber e v c.val).zero_mem

end Froberg.AttachedMultiplication
