module

public import Quartic.ClosedCovectorSpreading
public import Quartic.SliceFiniteModule
public import Quartic.RowMultiplicationCoordinates

@[expose] public section

/-!
Fixed-ambient closed covector equations for a varying presentation.
The original equations impose the shifted ambient kernel threshold, shared
child annihilation, and annihilation of every presentation product.
Auxiliary slices are appended as an explicitly separate linear family.
-/
noncomputable section
namespace Quartic.AmbientCovectorSpreading
open Module MvPolynomial BilinearCoefficientKernel BilinearCovectorCharts
set_option maxHeartbeats 1500000
variable {K : Type*} [Field K] {I : Type*} {a B T c q s d : ℕ}
variable (mu : (Fin B → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))

/-- The original equations, before adding the separately indexed slices. -/
abbrev Index (a B c q d : ℕ) :=
  ClosedCovectorEquations.Index a B q 0 (d+c) ⊕ (Fin c × Fin B)

def degree : Index a B c q d → ℕ
  | .inl j => ClosedCovectorEquations.degree j
  | .inr _ => 1

def equation (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K) :
    (j : Index a B c q d) → Forms K T (degree j)
  | .inl j => ClosedCovectorEquations.equation mu (Q,0) j
  | .inr jf => ClosedCovectorEquations.linearForm (mu (Pi.single jf.2 1) (E jf.1))

/-- The presentation equations annihilate all coefficient vectors, not just
the finitely many standard basis vectors used in the polynomial encoding. -/
theorem presentation_equations_iff (E : Fin c → Fin a → K) (ell : Fin T → K) :
    (∀ j f, eval ell (ClosedCovectorEquations.linearForm
      (mu (Pi.single f 1) (E j))).val = 0) ↔
      ∀ j f, covector ell (mu f (E j)) = 0 := by
  constructor
  · intro h j f
    rw [← (Pi.basisFun K (Fin B)).sum_equivFun f]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
      Pi.basisFun_apply,Pi.basisFun_equivFun]
    apply Finset.sum_eq_zero
    intro k _
    have hk : covector ell (mu (Pi.single k 1) (E j)) = 0 := by
      simpa only [ClosedCovectorEquations.eval_linearForm] using h j k
    rw [hk,smul_zero]
  · intro h j f
    simpa only [ClosedCovectorEquations.eval_linearForm] using h j (Pi.single f 1)

/-- Exact semantics of the original ambient homogeneous equation system.
Independence of E is not required for this literal statement. -/
theorem equations_iff (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K)
    (hd : d+c ≤ a) (ell : Fin T → K) :
    (∀ j : Index a B c q d, eval ell (equation mu E Q j).val = 0) ↔
      d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) ∧
      (∀ j f, covector ell (mu f (E j)) = 0) ∧
      (∀ i v, covector ell (mu (Q i) v) = 0) := by
  constructor
  · intro h
    have hclosed := (ClosedCovectorEquations.equations_iff mu (Q,0) hd ell).mp
      (fun j => h (.inl j))
    refine ⟨hclosed.1,?_,hclosed.2.1⟩
    apply (presentation_equations_iff mu E ell).mp
    intro j f
    exact h (.inr (j,f))
  · rintro ⟨hker,hE,hQ⟩ j
    cases j with
    | inl j =>
      exact (ClosedCovectorEquations.equations_iff mu (Q,0) hd ell).mpr
        ⟨hker,hQ,fun j => Fin.elim0 j⟩ j
    | inr jf =>
      exact (presentation_equations_iff mu E ell).mpr hE jf.1 jf.2

def finiteDegree (a B c q d : ℕ) : Fin (Fintype.card (Index a B c q d)) → ℕ :=
  fun j => degree ((Fintype.equivFin (Index a B c q d)).symm j)

def finiteOriginalEquations (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K) :
    (j : Fin (Fintype.card (Index a B c q d))) → Forms K T (finiteDegree a B c q d j) :=
  fun j => equation mu E Q ((Fintype.equivFin (Index a B c q d)).symm j)

theorem finite_original_equations_iff (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K)
    (hd : d+c ≤ a) (ell : Fin T → K) :
    (∀ j, eval ell (finiteOriginalEquations (d := d) mu E Q j).val = 0) ↔
      d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) ∧
      (∀ j f, covector ell (mu f (E j)) = 0) ∧
      (∀ i v, covector ell (mu (Q i) v) = 0) := by
  rw [← equations_iff mu E Q hd ell]
  constructor
  · intro h j
    have hj := h (Fintype.equivFin (Index a B c q d) j)
    exact (congrArg (fun i : Index a B c q d => eval ell (equation mu E Q i).val = 0)
      ((Fintype.equivFin (Index a B c q d)).symm_apply_apply j)).mp hj
  · intro h j
    exact h ((Fintype.equivFin (Index a B c q d)).symm j)

/-- Auxiliary target-vector annihilators remain separately available as
linear forms for the projective slice argument. -/
def slices (Z : Fin s → Fin T → K) : Fin s → Forms K T 1 :=
  fun j => ClosedCovectorEquations.linearForm (Z j)

def finiteEquationsDegree (a B c q s d : ℕ) :
    Fin (Fintype.card (Index a B c q d)+s) → ℕ :=
  SliceFiniteModule.slicedDegrees (s := s) (finiteDegree a B c q d)

/-- The exact combined family, with all original equations first and the
auxiliary slices last. -/
def finiteEquations (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K)
    (Z : Fin s → Fin T → K) :
    (j : Fin (Fintype.card (Index a B c q d)+s)) →
      Forms K T (finiteEquationsDegree a B c q s d j) :=
  SliceFiniteModule.slicedForms (finiteDegree a B c q d)
    (finiteOriginalEquations mu E Q) (slices Z)

/-- Appending slices is exact over every extension field. -/
theorem finite_equations_split {L : Type*} [Field L] [Algebra K L]
    (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K) (Z : Fin s → Fin T → K)
    (ell : Fin T → L) :
    (∀ j, aeval ell (finiteEquations (d := d) mu E Q Z j).val = 0) ↔
      (∀ j, aeval ell (finiteOriginalEquations (d := d) mu E Q j).val = 0) ∧
      (∀ j, aeval ell (slices Z j).val = 0) := by
  constructor
  · intro h
    constructor
    · intro j
      simpa only [finiteEquations,SliceFiniteModule.slicedForms,Fin.addCases_left] using
        h (Fin.castAdd s j)
    · intro j
      simpa only [finiteEquations,SliceFiniteModule.slicedForms,Fin.addCases_right] using
        h (Fin.natAdd (Fintype.card (Index a B c q d)) j)
  · rintro ⟨hf,hZ⟩ j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [finiteEquations,SliceFiniteModule.slicedForms,Fin.addCases_left] using hf i
    · intro i
      simpa only [finiteEquations,SliceFiniteModule.slicedForms,Fin.addCases_right] using hZ i

/-- Exact closed ambient-kernel and E/Q/slice annihilation semantics. -/
theorem finite_equations_iff (E : Fin c → Fin a → K) (Q : Fin q → Fin B → K)
    (Z : Fin s → Fin T → K) (hd : d+c ≤ a) (ell : Fin T → K) :
    (∀ j, eval ell (finiteEquations (d := d) mu E Q Z j).val = 0) ↔
      d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) ∧
      (∀ j f, covector ell (mu f (E j)) = 0) ∧
      (∀ i v, covector ell (mu (Q i) v) = 0) ∧
      (∀ j, covector ell (Z j) = 0) := by
  have h := finite_equations_split (d := d) mu E Q Z ell
  simp only [aeval_eq_eval,slices,ClosedCovectorEquations.eval_linearForm] at h
  rw [h,finite_original_equations_iff mu E Q hd ell]
  tauto

section Polynomiality
variable (E : (I → K) → Fin c → Fin a → K)
  (Q : (I → K) → Fin q → Fin B → K) (Z : (I → K) → Fin s → Fin T → K)
  (hE : ∀ j v, IsPolynomialFamily (fun p => E p j v))
  (hQ : ∀ i f, IsPolynomialFamily (fun p => Q p i f))
  (hZ : ∀ j k, IsPolynomialFamily (fun p => Z p j k))

include hE hQ in
theorem equation_polynomial (j : Index a B c q d) :
    IsPolynomialFamily (fun p => equation mu (E p) (Q p) j) := by
  cases j with
  | inl j =>
    exact ClosedCovectorSpreading.equation_polynomial (fun _ => mu)
      (fun _ _ _ => isPolynomialFamily_const _) Q hQ (fun _ => 0)
      (fun _ _ => isPolynomialFamily_const _) j
  | inr jf =>
    apply ClosedCovectorSpreading.linearForm_polynomial
    intro k
    exact ClosedCovectorSpreading.mixed_coordinate_polynomial (fun _ => mu.flip)
      (fun _ _ _ => isPolynomialFamily_const _) E hE jf.1 jf.2 k

include hE hQ in
theorem finiteOriginalEquations_polynomial
    (j : Fin (Fintype.card (Index a B c q d))) :
    IsPolynomialFamily (fun p => finiteOriginalEquations (d := d) mu (E p) (Q p) j) :=
  equation_polynomial mu E Q hE hQ _

include hZ in
theorem slices_polynomial (j : Fin s) : IsPolynomialFamily (fun p => slices (Z p) j) :=
  ClosedCovectorSpreading.linearForm_polynomial _ (hZ j)

include hE hQ hZ in
theorem finiteEquations_polynomial
    (j : Fin (Fintype.card (Index a B c q d)+s)) :
    IsPolynomialFamily (fun p => finiteEquations (d := d) mu (E p) (Q p) (Z p) j) := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    let A : Forms K T (finiteDegree a B c q d i) →ₗ[K]
        Forms K T (finiteEquationsDegree a B c q s d (Fin.castAdd s i)) :=
      Submodule.inclusion (by
        simp only [finiteEquationsDegree,SliceFiniteModule.slicedDegrees,Fin.addCases_left]
        exact le_rfl)
    have h := (finiteOriginalEquations_polynomial mu E Q hE hQ i).linear_comp A
    convert h using 1
    funext p
    apply Subtype.ext
    simp only [finiteEquations,SliceFiniteModule.slicedForms,Fin.addCases_left]
    rfl
  · intro i
    let A : Forms K T 1 →ₗ[K]
        Forms K T (finiteEquationsDegree a B c q s d
          (Fin.natAdd (Fintype.card (Index a B c q d)) i)) :=
      Submodule.inclusion (by
        simp only [finiteEquationsDegree,SliceFiniteModule.slicedDegrees,Fin.addCases_right]
        exact le_rfl)
    have h := (slices_polynomial Z hZ i).linear_comp A
    convert h using 1
    funext p
    apply Subtype.ext
    simp only [finiteEquations,SliceFiniteModule.slicedForms,Fin.addCases_right]
    rfl

include hE hQ hZ in
/-- The actual fixed-ambient presentation equations spread from geometric
emptiness on a principal open in E/Q/Z parameters. -/
theorem principal_open_empty_fiber {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (p₀ : I → K)
    (hempty : ∀ ell : Fin T → L,
      (∀ j, aeval ell (finiteOriginalEquations (d := d) mu (E p₀) (Q p₀) j).val = 0) →
      (∀ j, aeval ell (slices (Z p₀) j).val = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p, eval p D ≠ 0 →
      ∀ ell : Fin T → L,
        (∀ j, aeval ell (finiteOriginalEquations (d := d) mu (E p) (Q p) j).val = 0) →
        (∀ j, aeval ell (slices (Z p) j).val = 0) → ell = 0 := by
  obtain ⟨D,hD,hgood⟩ := HomogeneousEmptyFiberOpen.principal_open_empty_fiber (L := L)
    (finiteEquationsDegree a B c q s d)
    (fun j p => finiteEquations mu (E p) (Q p) (Z p) j)
    (finiteEquations_polynomial mu E Q Z hE hQ hZ) p₀ (by
      intro ell h
      have hsplit := (finite_equations_split mu (E p₀) (Q p₀) (Z p₀) ell).mp h
      exact hempty ell hsplit.1 hsplit.2)
  refine ⟨D,hD,?_⟩
  intro p hp ell hf hZell
  exact hgood p hp ell ((finite_equations_split mu (E p) (Q p) (Z p) ell).mpr ⟨hf,hZell⟩)

include hE hQ hZ in
/-- Actual ambient relation-map semantics on the resulting base-field open. -/
theorem principal_open_closed {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (hd : d+c ≤ a) (p₀ : I → K)
    (hempty : ∀ ell : Fin T → L,
      (∀ j, aeval ell (finiteOriginalEquations (d := d) mu (E p₀) (Q p₀) j).val = 0) →
      (∀ j, aeval ell (slices (Z p₀) j).val = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p, eval p D ≠ 0 →
      ∀ ell : Fin T → K,
        d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
        (∀ j f, covector ell (mu f (E p j)) = 0) →
        (∀ i v, covector ell (mu (Q p i) v) = 0) →
        (∀ j, covector ell (Z p j) = 0) → ell = 0 := by
  obtain ⟨D,hD,hgood⟩ := principal_open_empty_fiber mu E Q Z hE hQ hZ p₀ hempty
  refine ⟨D,hD,?_⟩
  intro p hp ell hker hEell hQell hZell
  have hf := (finite_original_equations_iff mu (E p) (Q p) hd ell).mpr ⟨hker,hEell,hQell⟩
  have hZf : ∀ j, eval ell (slices (Z p) j).val = 0 := by
    intro j
    simpa only [slices,ClosedCovectorEquations.eval_linearForm] using hZell j
  have hz := hgood p hp (fun i => algebraMap K L (ell i)) (by
    intro j
    have he := MvPolynomial.comp_aeval_apply ell (Algebra.ofId K L)
      (finiteOriginalEquations (d := d) mu (E p) (Q p) j).val
    exact he.symm.trans (by rw [aeval_eq_eval,hf j,map_zero])) (by
    intro j
    have he := MvPolynomial.comp_aeval_apply ell (Algebra.ofId K L) (slices (Z p) j).val
    exact he.symm.trans (by rw [aeval_eq_eval,hZf j,map_zero]))
  funext i
  apply (algebraMap K L).injective
  simpa only [Pi.zero_apply,map_zero] using congrFun hz i

include hE hQ hZ in
/-- Over an algebraically closed base, the witness and conclusion both use
only the actual ambient kernel and annihilation conditions. -/
theorem principal_open_closed_of_witness [IsAlgClosed K]
    (hd : d+c ≤ a) (p₀ : I → K)
    (hwitness : ∀ ell : Fin T → K,
      d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
      (∀ j f, covector ell (mu f (E p₀ j)) = 0) →
      (∀ i v, covector ell (mu (Q p₀ i) v) = 0) →
      (∀ j, covector ell (Z p₀ j) = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p, eval p D ≠ 0 →
      ∀ ell : Fin T → K,
        d+c ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
        (∀ j f, covector ell (mu f (E p j)) = 0) →
        (∀ i v, covector ell (mu (Q p i) v) = 0) →
        (∀ j, covector ell (Z p j) = 0) → ell = 0 := by
  apply principal_open_closed (L := K) mu E Q Z hE hQ hZ hd p₀
  intro ell hf hZell
  have hh := (finite_original_equations_iff mu (E p₀) (Q p₀) hd ell).mp
    (by simpa only [aeval_eq_eval] using hf)
  apply hwitness ell hh.1 hh.2.1 hh.2.2
  intro j
  simpa only [aeval_eq_eval,slices,ClosedCovectorEquations.eval_linearForm] using hZell j

end Polynomiality

section ActualRows
open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
variable {m : ℕ}

/-- Fixed monomial coordinates of actual mixed columns. -/
def rowPresentation (E : Fin c → Rows K m 1) : Fin c → Fin (RowCount m 1) → K :=
  fun j => rowFiniteEquiv (E j)

/-- Fixed monomial coordinates of the shared actual child quadrics. -/
def rowChildren (Q : Fin q → Forms K m 2) : Fin q → Fin (FormCount m 2) → K :=
  fun i => finiteEquiv (Q i)

/-- Fixed monomial coordinates of the actual ambient target slices. -/
def rowSlices (Z : Fin s → Rows K m 3) : Fin s → Fin (RowCount m 3) → K :=
  fun j => rowFiniteEquiv (Z j)

variable (E : (I → K) → Fin c → Rows K m 1)
  (Q : (I → K) → Fin q → Forms K m 2) (Z : (I → K) → Fin s → Rows K m 3)
  (hE : ∀ j, IsPolynomialFamily (fun p => E p j))
  (hQ : ∀ i, IsPolynomialFamily (fun p => Q p i))
  (hZ : ∀ j, IsPolynomialFamily (fun p => Z p j))

include hE hQ hZ in
/-- Actual polynomial row, quadric, and slice families satisfy the literal
ambient-equation polynomiality requirement in fixed monomial coordinates. -/
theorem rowEquations_polynomial
    (j : Fin (Fintype.card (Index (RowCount m 1) (FormCount m 2) c q d)+s)) :
    IsPolynomialFamily (fun p => finiteEquations (d := d) coordinate
      (rowPresentation (E p)) (rowChildren (Q p)) (rowSlices (Z p)) j) := by
  apply finiteEquations_polynomial
  · intro j v
    exact ((hE j).linear_comp rowFiniteEquiv.toLinearMap).linear_comp (LinearMap.proj v)
  · intro i f
    exact ((hQ i).linear_comp finiteEquiv.toLinearMap).linear_comp (LinearMap.proj f)
  · intro j k
    exact ((hZ j).linear_comp rowFiniteEquiv.toLinearMap).linear_comp (LinearMap.proj k)

include hE hQ hZ in
/-- The principal open for the fixed actual row multiplication and varying
actual mixed columns, shared quadrics, and target slices. No quotient basis
is chosen, and the presentation annihilation condition uses all quadrics. -/
theorem principal_open_rows {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (hd : d+c ≤ RowCount m 1) (p₀ : I → K)
    (hempty : ∀ ell : Fin (RowCount m 3) → L,
      (∀ j, aeval ell (finiteOriginalEquations (d := d) coordinate
        (rowPresentation (E p₀)) (rowChildren (Q p₀)) j).val = 0) →
      (∀ j, aeval ell (slices (rowSlices (Z p₀)) j).val = 0) → ell = 0) :
    ∃ D : MvPolynomial I K, eval p₀ D ≠ 0 ∧ ∀ p, eval p D ≠ 0 →
      ∀ ell : Fin (RowCount m 3) → K,
        d+c ≤ finrank K (LinearMap.ker (relationMap coordinate ell)) →
        (∀ j f, covector ell (rowFiniteEquiv (multiplication f (E p j))) = 0) →
        (∀ i v, covector ell (rowFiniteEquiv (multiplication (Q p i) v)) = 0) →
        (∀ j, covector ell (rowFiniteEquiv (Z p j)) = 0) → ell = 0 := by
  obtain ⟨D,hD,hgood⟩ := principal_open_closed coordinate
    (fun p => rowPresentation (E p)) (fun p => rowChildren (Q p))
    (fun p => rowSlices (Z p))
    (fun j v => ((hE j).linear_comp rowFiniteEquiv.toLinearMap).linear_comp (LinearMap.proj v))
    (fun i f => ((hQ i).linear_comp finiteEquiv.toLinearMap).linear_comp (LinearMap.proj f))
    (fun j k => ((hZ j).linear_comp rowFiniteEquiv.toLinearMap).linear_comp (LinearMap.proj k))
    hd p₀ hempty
  refine ⟨D,hD,?_⟩
  intro p hp ell hker hEell hQell hZell
  apply hgood p hp ell hker
  · intro j f
    simpa only [rowPresentation,coordinate_apply,LinearEquiv.symm_apply_apply] using
      hEell j (finiteEquiv.symm f)
  · intro i v
    simpa only [rowChildren,coordinate_apply,LinearEquiv.symm_apply_apply] using
      hQell i (rowFiniteEquiv.symm v)
  · exact hZell

end ActualRows

end Quartic.AmbientCovectorSpreading
