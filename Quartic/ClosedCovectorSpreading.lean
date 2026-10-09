module

public import Quartic.ConvolutionClosedSlices
public import Quartic.HomogeneousEmptyFiberOpen

@[expose] public section

/-!
Polynomiality and empty-fiber spreading for the literal closed covector
equations.  The coefficient conditions concern μ, Q, and Z individually;
polynomiality of their determinant and annihilator equations is proved.
-/
noncomputable section
namespace Quartic.ClosedCovectorSpreading
open Module MvPolynomial ClosedCovectorEquations BilinearCoefficientKernel BilinearCovectorCharts
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {I : Type*} {a B T q s d : ℕ}

/-- A linear covector equation varies polynomially with its actual vector
coordinates. -/
theorem linearForm_polynomial (y : (I → K) → Fin T → K)
    (hy : ∀ k, IsPolynomialFamily (fun p => y p k)) :
    IsPolynomialFamily (fun p => linearForm (y p)) := by
  have h := IsPolynomialFamily.sum (fun k => (hy k).smul
    (isPolynomialFamily_const (⟨X k,isHomogeneous_X K k⟩ : Forms K T 1)))
  convert h using 1
  funext p
  apply Subtype.ext
  simp only [linearForm,Submodule.coe_sum,Submodule.coe_smul,smul_eq_C_mul]

/-- Evaluating μ on a varying child vector and a fixed source basis vector
is polynomial, as shown by the literal coefficient sum. -/
theorem mixed_coordinate_polynomial
    (mu : (I → K) → (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (Q : (I → K) → Fin q → Fin B → K)
    (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f)) (i : Fin q) (v : Fin a) (k : Fin T) :
    IsPolynomialFamily (fun p => mu p (Q p i) (Pi.single v 1) k) := by
  have h := IsPolynomialFamily.sum (fun f => (hQ i f).smul (hmu f v k))
  convert h using 1
  funext p
  conv_lhs => rw [← (Pi.basisFun K (Fin B)).sum_equivFun (Q p i)]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    Pi.basisFun_apply,Pi.basisFun_equivFun,LinearEquiv.refl_apply,Finset.sum_apply,Pi.smul_apply]

/-- Every actual minor, shared-child equation, and auxiliary slice equation
varies polynomially in the supplied coefficients. -/
theorem equation_polynomial
    (mu : (I → K) → (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (Q : (I → K) → Fin q → Fin B → K)
    (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f))
    (Z : (I → K) → Fin s → Fin T → K)
    (hZ : ∀ j k, IsPolynomialFamily (fun p => Z p j k))
    (j : Index a B q s d) :
    IsPolynomialFamily (fun p => equation (mu p) (Q p,Z p) j) := by
  cases j with
  | inl uv =>
    exact BilinearImageMinors.determinantForm_polynomial
      (fun p i j => linearForm (mu p (Pi.single (uv.2 j) 1) (Pi.single (uv.1 i) 1)))
      (fun i j => linearForm_polynomial _ (hmu (uv.2 j) (uv.1 i)))
  | inr j =>
    cases j with
    | inl iv =>
      exact linearForm_polynomial _ (mixed_coordinate_polynomial mu hmu Q hQ iv.1 iv.2)
    | inr h => exact linearForm_polynomial _ (hZ h)

/-- The exact finite dependent family used by the empty-fiber theorem. -/
theorem finiteEquations_polynomial
    (mu : (I → K) → (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (Q : (I → K) → Fin q → Fin B → K)
    (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f))
    (Z : (I → K) → Fin s → Fin T → K)
    (hZ : ∀ j k, IsPolynomialFamily (fun p => Z p j k))
    (j : Fin (Fintype.card (Index a B q s d))) :
    IsPolynomialFamily (fun p => finiteEquations (d := d) (mu p) (Q p,Z p) j) :=
  equation_polynomial mu hmu Q hQ Z hZ _

/-- Actual closed covector equations remain geometrically empty throughout
a principal open whose polynomial is nonzero at the given witness. -/
theorem principal_open_empty_fiber {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (mu : (I → K) → (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (Q : (I → K) → Fin q → Fin B → K)
    (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f))
    (Z : (I → K) → Fin s → Fin T → K)
    (hZ : ∀ j k, IsPolynomialFamily (fun p => Z p j k))
    (p₀ : I → K)
    (hempty : ∀ ell : Fin T → L,
      (∀ j, aeval ell (finiteEquations (d := d) (mu p₀) (Q p₀,Z p₀) j).val = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧
      ∀ p, eval p D ≠ 0 → ∀ ell : Fin T → L,
        (∀ j, aeval ell (finiteEquations (d := d) (mu p) (Q p,Z p) j).val = 0) → ell = 0 :=
  HomogeneousEmptyFiberOpen.principal_open_empty_fiber
    (finiteDegree a B q s d)
    (fun j p => finiteEquations (mu p) (Q p,Z p) j)
    (finiteEquations_polynomial mu hmu Q hQ Z hZ) p₀ hempty

/-- The geometric open also excludes every actual base-field covector whose
relation kernel meets the closed threshold and which annihilates Q and Z. -/
theorem principal_open_closed {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (mu : (I → K) → (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (Q : (I → K) → Fin q → Fin B → K)
    (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f))
    (Z : (I → K) → Fin s → Fin T → K)
    (hZ : ∀ j k, IsPolynomialFamily (fun p => Z p j k))
    (hd : d ≤ a) (p₀ : I → K)
    (hempty : ∀ ell : Fin T → L,
      (∀ j, aeval ell (finiteEquations (d := d) (mu p₀) (Q p₀,Z p₀) j).val = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧
      ∀ p, eval p D ≠ 0 → ∀ ell : Fin T → K,
        d ≤ finrank K (LinearMap.ker (relationMap (mu p) ell)) →
        (∀ i v, covector ell (mu p (Q p i) v) = 0) →
        (∀ j, covector ell (Z p j) = 0) → ell = 0 := by
  obtain ⟨D,hD,hgood⟩ := principal_open_empty_fiber mu hmu Q hQ Z hZ p₀ hempty
  refine ⟨D,hD,?_⟩
  intro p hp ell hker hQell hZell
  have heq := (finite_equations_iff (mu p) (Q p,Z p) hd ell).mpr ⟨hker,hQell,hZell⟩
  have hz := hgood p hp (fun i => algebraMap K L (ell i)) (by
    intro j
    have he := MvPolynomial.comp_aeval_apply ell (Algebra.ofId K L)
      (finiteEquations (d := d) (mu p) (Q p,Z p) j).val
    exact he.symm.trans (by rw [aeval_eq_eval,heq j,map_zero]))
  funext i
  apply (algebraMap K L).injective
  simpa only [Pi.zero_apply,map_zero] using congrFun hz i

/-- Over an algebraically closed base field, the witness may be stated
directly using the actual relation map and the actual annihilation equations. -/
theorem principal_open_closed_of_witness [IsAlgClosed K]
    (mu : (I → K) → (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (hmu : ∀ f v k, IsPolynomialFamily (fun p => mu p (Pi.single f 1) (Pi.single v 1) k))
    (Q : (I → K) → Fin q → Fin B → K)
    (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f))
    (Z : (I → K) → Fin s → Fin T → K)
    (hZ : ∀ j k, IsPolynomialFamily (fun p => Z p j k))
    (hd : d ≤ a) (p₀ : I → K)
    (hwitness : ∀ ell : Fin T → K,
      d ≤ finrank K (LinearMap.ker (relationMap (mu p₀) ell)) →
      (∀ i v, covector ell (mu p₀ (Q p₀ i) v) = 0) →
      (∀ j, covector ell (Z p₀ j) = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧
      ∀ p, eval p D ≠ 0 → ∀ ell : Fin T → K,
        d ≤ finrank K (LinearMap.ker (relationMap (mu p) ell)) →
        (∀ i v, covector ell (mu p (Q p i) v) = 0) →
        (∀ j, covector ell (Z p j) = 0) → ell = 0 := by
  apply principal_open_closed (L := K) mu hmu Q hQ Z hZ hd p₀
  intro ell heq
  have h := (finite_equations_iff (mu p₀) (Q p₀,Z p₀) hd ell).mp
    (by simpa only [aeval_eq_eval] using heq)
  exact hwitness ell h.1 h.2.1 h.2.2

end Quartic.ClosedCovectorSpreading
