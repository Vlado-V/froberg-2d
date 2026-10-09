module

public import Quartic.BilinearImageMinors
public import Quartic.BilinearScalarExtension
public import Quartic.SubspaceMinorCoordinates

@[expose] public section

/-! # Actual homogeneous equations for failure of a bilinear expansion bound -/
noncomputable section
namespace Quartic.BilinearExpansionEquations
open Module Matrix MvPolynomial SubspaceMinorCoordinates BilinearImageMinors
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {a b t d e : ℕ} {I : Type*}

abbrev ProjectiveCount (a d : ℕ) := Fintype.card (RowChoice a d)

def rowIndex (a d : ℕ) : RowChoice a d ≃ Fin (ProjectiveCount a d) := Fintype.equivFin _

/-- Decode finite projective coordinates without changing the field. -/
def decode (q : Fin (ProjectiveCount a d) → L) : RowChoice a d → L :=
  fun J => q (rowIndex a d J)

theorem decode_eq_zero_iff (q : Fin (ProjectiveCount a d) → L) : decode q = 0 ↔ q = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h ((rowIndex a d).symm i)
    simpa only [decode, Equiv.apply_symm_apply, Pi.zero_apply] using hi
  · rintro rfl
    rfl

/-- One projective coordinate as an actual degree-one form. -/
def variableForm (J : RowChoice a d) : Forms K (ProjectiveCount a d) 1 :=
  ⟨X (rowIndex a d J), isHomogeneous_X _ _⟩

@[simp] theorem aeval_variableForm (q : Fin (ProjectiveCount a d) → L) (J : RowChoice a d) :
    aeval q (variableForm (K := K) J).val = decode q J := by
  simp [variableForm, decode]

/-- The selected-pivot identities are homogeneous linear equations. -/
def selectedEquation (J : RowChoice a d) (i j : Fin d) : Forms K (ProjectiveCount a d) 1 :=
  variableForm (Function.update J j (J i)) - if i=j then variableForm J else 0

@[simp] theorem aeval_selectedEquation (q : Fin (ProjectiveCount a d) → L)
    (J : RowChoice a d) (i j : Fin d) :
    aeval q (selectedEquation (K := K) J i j).val =
      reconstruction (decode q) J (J i) j - if i=j then decode q J else 0 := by
  classical
  by_cases h : i=j <;> simp [selectedEquation, h, reconstruction, aeval_variableForm]

/-- Entries of the image matrix are linear in the projective coordinates. -/
def entry (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (J : RowChoice a d) (k : Fin t) (col : Fin d × Fin b) :
    Forms K (ProjectiveCount a d) 1 :=
  ∑ v, mu (Pi.single col.2 1) (Pi.single v 1) k •
    variableForm (Function.update J col.1 v)

theorem aeval_entry (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (q : Fin (ProjectiveCount a d) → L) (J : RowChoice a d) (k : Fin t) (col : Fin d × Fin b) :
    aeval q (entry mu J k col).val =
      imageMatrix (BilinearScalarExtension.extend (L := L) mu)
        (reconstruction (decode q) J).col k col := by
  simp only [entry, Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def, map_sum, map_mul,
    AlgHom.commutes, aeval_variableForm, imageMatrix,
    BilinearScalarExtension.extend_basis_left, Matrix.col_apply, reconstruction]

theorem entry_polynomial
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (J : RowChoice a d) (k : Fin t) (col : Fin d × Fin b) :
    IsPolynomialFamily (fun p => entry (mu p) J k col) :=
  IsPolynomialFamily.sum (fun v => (hmu col.2 v k).smul
    (isPolynomialFamily_const (variableForm (Function.update J col.1 v))))

/-- Every e-by-e image minor is a homogeneous equation of degree e. -/
def minorEquation (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (J : RowChoice a d) (u : Fin e → Fin t) (v : Fin e → Fin d × Fin b) :
    Forms K (ProjectiveCount a d) e :=
  determinantForm (fun i j => entry mu J (u i) (v j))

theorem aeval_minorEquation
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (q : Fin (ProjectiveCount a d) → L) (J : RowChoice a d)
    (u : Fin e → Fin t) (v : Fin e → Fin d × Fin b) :
    aeval q (minorEquation mu J u v).val =
      ((imageMatrix (BilinearScalarExtension.extend (L := L) mu)
        (reconstruction (decode q) J).col).submatrix u v).det := by
  change aeval q (Matrix.det (fun i j => (entry mu J (u i) (v j)).val)) = _
  have hm := (aeval q).toRingHom.map_det
    (fun i j => (entry mu J (u i) (v j)).val : Matrix (Fin e) (Fin e) _)
  exact hm.trans (by
    congr 1
    ext i j
    exact aeval_entry mu q J (u i) (v j))

theorem minorEquation_polynomial
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (J : RowChoice a d) (u : Fin e → Fin t) (v : Fin e → Fin d × Fin b) :
    IsPolynomialFamily (fun p => minorEquation (mu p) J u v) :=
  determinantForm_polynomial (fun p i j => entry (mu p) J (u i) (v j))
    (fun i j => entry_polynomial mu hmu J (u i) (v j))

/-- A finite list with the exact linear and degree-e parts kept distinct. -/
abbrev EquationIndex (a b t d e : ℕ) :=
  (RowChoice a d × Fin d × Fin d) ⊕
    (RowChoice a d × (Fin e → Fin t) × (Fin e → Fin d × Fin b))

def equationDegree : EquationIndex a b t d e → ℕ
  | .inl _ => 1
  | .inr _ => e

def equation (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    (x : EquationIndex a b t d e) → Forms K (ProjectiveCount a d) (equationDegree x)
  | .inl x => selectedEquation x.1 x.2.1 x.2.2
  | .inr x => minorEquation mu x.1 x.2.1 x.2.2

theorem equation_polynomial
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (x : EquationIndex a b t d e) : IsPolynomialFamily (fun p => equation (mu p) x) := by
  cases x with
  | inl x => exact isPolynomialFamily_const _
  | inr x => exact minorEquation_polynomial mu hmu x.1 x.2.1 x.2.2

/-- The finite polynomial system says exactly Selected plus a low image rank in every pivot. -/
theorem equations_iff
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (q : Fin (ProjectiveCount a d) → L) :
    (∀ x : EquationIndex a b t d e, aeval q (equation mu x).val = 0) ↔
      Selected (decode q) ∧ ∀ J : RowChoice a d,
        (imageMatrix (BilinearScalarExtension.extend (L := L) mu)
          (reconstruction (decode q) J).col).rank < e := by
  constructor
  · intro h
    constructor
    · intro J i j
      exact sub_eq_zero.mp ((aeval_selectedEquation q J i j).symm.trans (h (.inl (J,i,j))))
    · intro J
      apply (rank_lt_iff_minors_zero _ e).mpr
      intro u v
      exact (aeval_minorEquation mu q J u v).symm.trans (h (.inr (J,u,v)))
  · rintro ⟨hs,hr⟩ x
    cases x with
    | inl x =>
      change aeval q (selectedEquation (K := K) x.1 x.2.1 x.2.2).val = 0
      rw [aeval_selectedEquation,hs,sub_self]
    | inr x =>
      change aeval q (minorEquation mu x.1 x.2.1 x.2.2).val = 0
      rw [aeval_minorEquation]
      exact (rank_lt_iff_minors_zero _ e).mp (hr x.1) x.2.1 x.2.2

end Quartic.BilinearExpansionEquations
