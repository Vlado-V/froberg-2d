import Quartic.Homogeneous

/-! # Explicit monomial coefficients compatible with every field extension -/
noncomputable section
namespace Quartic.HomogeneousCoefficientCoordinates
open Module MvPolynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m d : ℕ}

abbrev Exponent (m d : ℕ) := {e : Fin m →₀ ℕ // e.degree = d}

instance exponentFintype (m d : ℕ) : Fintype (Exponent m d) :=
  Fintype.ofEquiv (Sym (Fin m) d) (exponentEquiv m d)

/-- Every coordinate is a literal coefficient of the polynomial. -/
def coefficients : Forms K m d →ₗ[K] (Exponent m d → K) :=
  LinearMap.pi (fun e => (MvPolynomial.lcoeff K e.val).comp (Forms K m d).subtype)

@[simp] theorem coefficients_apply (f : Forms K m d) (e : Exponent m d) :
    coefficients f e = f.val.coeff e.val := rfl

/-- Reconstruct the actual polynomial, using each degree-d monomial once. -/
def polynomial (x : Exponent m d → K) : Forms K m d :=
  ⟨∑ e, monomial e.val (x e), IsHomogeneous.sum _ _ d
    (fun e _ => isHomogeneous_monomial _ e.property)⟩

@[simp] theorem coefficients_polynomial (x : Exponent m d → K) :
    coefficients (polynomial x) = x := by
  classical
  funext e
  simp only [coefficients_apply, polynomial, coeff_sum, coeff_monomial]
  have he (f : Exponent m d) : f.val = e.val ↔ f = e := Subtype.ext_iff.symm
  simp_rw [he]
  simp

theorem polynomial_coefficients (f : Forms K m d) : polynomial (coefficients f) = f := by
  classical
  apply Subtype.ext
  apply MvPolynomial.ext
  intro e
  by_cases he : e.degree = d
  · exact congrFun (coefficients_polynomial (coefficients f)) ⟨e,he⟩
  · have hz : f.val.coeff e = 0 := f.property.coeff_eq_zero he
    rw [hz]
    change (∑ i : Exponent m d, monomial i.val (coefficients f i)).coeff e = 0
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hne : i.val ≠ e := fun h => he (h ▸ i.property)
    simp [coeff_monomial,hne]

/-- Canonical coefficient coordinates have an explicit polynomial inverse. -/
def equiv : Forms K m d ≃ₗ[K] (Exponent m d → K) :=
  { coefficients with
    invFun := polynomial
    left_inv := polynomial_coefficients
    right_inv := coefficients_polynomial }

@[simp] theorem equiv_apply (f : Forms K m d) (e : Exponent m d) :
    equiv f e = f.val.coeff e.val := rfl

@[simp] theorem equiv_symm_apply_val (x : Exponent m d → K) :
    (equiv.symm x).val = ∑ e, monomial e.val (x e) := rfl

/-- Extend the polynomial coefficients without changing any exponent. -/
def mapForm (f : Forms K m d) : Forms L m d :=
  ⟨MvPolynomial.map (algebraMap K L) f.val, f.property.map _⟩

@[simp] theorem coefficients_mapForm (f : Forms K m d) (e : Exponent m d) :
    coefficients (mapForm (L := L) f) e = algebraMap K L (coefficients f e) := by
  simp [coefficients_apply, mapForm, coeff_map]

@[simp] theorem equiv_mapForm (f : Forms K m d) (e : Exponent m d) :
    equiv (mapForm (L := L) f) e = algebraMap K L (equiv f e) :=
  coefficients_mapForm f e

theorem mapForm_equiv_symm (x : Exponent m d → K) :
    mapForm (L := L) (equiv.symm x) = equiv.symm (fun e => algebraMap K L (x e)) := by
  apply equiv.injective
  funext e
  rw [equiv_mapForm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- A field-independent finite ordering of coefficient positions. -/
def reindex (J : Type*) [Fintype J] : (J → K) ≃ₗ[K] (Fin (Fintype.card J) → K) where
  toFun x i := x ((Fintype.equivFin J).symm i)
  invFun x j := x (Fintype.equivFin J j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteEquiv : Forms K m d ≃ₗ[K] (Fin (Fintype.card (Exponent m d)) → K) :=
  equiv.trans (reindex (Exponent m d))

@[simp] theorem finiteEquiv_mapForm (f : Forms K m d)
    (i : Fin (Fintype.card (Exponent m d))) :
    finiteEquiv (mapForm (L := L) f) i = algebraMap K L (finiteEquiv f i) :=
  equiv_mapForm f _

end Quartic.HomogeneousCoefficientCoordinates
