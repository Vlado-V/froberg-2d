module

public import Quartic.BilinearExpansionEquations
public import Quartic.SubspaceMinorContainment

@[expose] public section

/-! # Homogeneous equations for low bilinear images containing a varying presentation -/
noncomputable section
namespace Quartic.BilinearContainingEquations
open Module Matrix MvPolynomial SubspaceMinorCoordinates SubspaceMinorContainment
open BilinearExpansionEquations BilinearImageMinors
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {a b t c d e : ℕ} {I : Type*}

/-- The coefficients of a varying presentation multiply linear projective coordinates. -/
def containmentEquation (E : Matrix (Fin a) (Fin c) K) (J : RowChoice a d)
    (j : Fin c) (k : Fin a) : Forms K (ProjectiveCount a d) 1 :=
  E k j • variableForm J - ∑ i, E (J i) j • variableForm (Function.update J i k)

theorem aeval_containmentEquation (E : Matrix (Fin a) (Fin c) K)
    (q : Fin (ProjectiveCount a d) → L) (J : RowChoice a d) (j : Fin c) (k : Fin a) :
    aeval q (containmentEquation E J j k).val =
      decode q J * algebraMap K L (E k j) -
        (reconstruction (decode q) J *ᵥ (fun i => algebraMap K L (E (J i) j))) k := by
  simp only [containmentEquation, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum,
    Algebra.smul_def, map_sub, map_mul, map_sum, AlgHom.commutes, aeval_variableForm,
    Matrix.mulVec, dotProduct, reconstruction]
  congr 1
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _

theorem containmentEquation_polynomial (E : (I → K) → Matrix (Fin a) (Fin c) K)
    (hE : ∀ k j, IsPolynomialFamily (fun p => E p k j))
    (J : RowChoice a d) (j : Fin c) (k : Fin a) :
    IsPolynomialFamily (fun p => containmentEquation (E p) J j k) := by
  have hleft := (hE k j).smul (isPolynomialFamily_const (variableForm (K := K) J))
  have hright := IsPolynomialFamily.sum (fun i => (hE (J i) j).smul
    (isPolynomialFamily_const (variableForm (K := K) (Function.update J i k))))
  have h := hleft.add (hright.linear_comp (-LinearMap.id))
  simpa only [containmentEquation,LinearMap.neg_apply,LinearMap.id_apply,sub_eq_add_neg] using h

theorem containment_equations_iff (E : Matrix (Fin a) (Fin c) K)
    (q : Fin (ProjectiveCount a d) → L) :
    (∀ J : RowChoice a d, ∀ j k, aeval q (containmentEquation E J j k).val = 0) ↔
      ContainsMatrix (decode q) (E.map (algebraMap K L)) := by
  constructor
  · intro h j J
    funext k
    exact sub_eq_zero.mp ((aeval_containmentEquation E q J j k).symm.trans (h J j k))
  · intro h J j k
    rw [aeval_containmentEquation]
    exact sub_eq_zero.mpr (congrFun (h j J) k)

/-- The entire system remains finite and homogeneous in the projective variables. -/
abbrev Index (a b t c d e : ℕ) :=
  (RowChoice a d × Fin c × Fin a) ⊕ BilinearExpansionEquations.EquationIndex a b t d e

def degree : Index a b t c d e → ℕ
  | .inl _ => 1
  | .inr x => equationDegree x

def equation (E : Matrix (Fin a) (Fin c) K)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K)) :
    (x : Index a b t c d e) → Forms K (ProjectiveCount a d) (degree x)
  | .inl x => containmentEquation E x.1 x.2.1 x.2.2
  | .inr x => BilinearExpansionEquations.equation mu x

theorem equation_polynomial (E : (I → K) → Matrix (Fin a) (Fin c) K)
    (hE : ∀ k j, IsPolynomialFamily (fun p => E p k j))
    (mu : (I → K) → (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (x : Index a b t c d e) : IsPolynomialFamily (fun p => equation (E p) (mu p) x) := by
  cases x with
  | inl x => exact containmentEquation_polynomial E hE x.1 x.2.1 x.2.2
  | inr x => exact BilinearExpansionEquations.equation_polynomial mu hmu x

/-- Exact interpretation of all equations over the explicitly specified extension field. -/
theorem equations_iff (E : Matrix (Fin a) (Fin c) K)
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin t → K))
    (q : Fin (ProjectiveCount a d) → L) :
    (∀ x : Index a b t c d e, aeval q (equation E mu x).val = 0) ↔
      ContainsMatrix (decode q) (E.map (algebraMap K L)) ∧ Selected (decode q) ∧
        ∀ J : RowChoice a d,
          (imageMatrix (BilinearScalarExtension.extend (L := L) mu)
            (reconstruction (decode q) J).col).rank < e := by
  constructor
  · intro h
    refine ⟨(containment_equations_iff E q).mp (fun J j k => h (.inl (J,j,k))), ?_⟩
    exact (BilinearExpansionEquations.equations_iff mu q).mp (fun x => h (.inr x))
  · rintro ⟨hE,hs,hr⟩ x
    cases x with
    | inl x => exact (containment_equations_iff E q).mpr hE x.1 x.2.1 x.2.2
    | inr x => exact (BilinearExpansionEquations.equations_iff mu q).mpr ⟨hs,hr⟩ x

end Quartic.BilinearContainingEquations
