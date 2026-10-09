module

public import Quartic.ConvolutionPresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# The dual of the actual convolution cokernel

The dual is canonically the annihilator of the polynomial presentation image.
Testing that annihilator on source monomials gives an explicit coefficient
recurrence. The monomials span the actual homogeneous spaces, so this is an
if-and-only-if criterion, not merely a necessary condition.
-/

namespace Quartic.ConvolutionDual

noncomputable section

open MvPolynomial Quartic.ConvolutionPresentation

variable {K : Type*} [Field K] {t j : ℕ}

/-- The actual presentation-image annihilator in the dual target. -/
def annihilator (K : Type*) [Field K] (t j : ℕ) :
    Submodule K (Module.Dual K (Target K t (j + 1))) :=
  (LinearMap.range (presentation (K := K) (t := t) (j := j))).dualAnnihilator

/-- The canonical dual-cokernel identification. -/
def cokernelDualEquiv (K : Type*) [Field K] (t j : ℕ) :=
  (LinearMap.range (presentation (K := K) (t := t) (j := j))).dualQuotEquivDualAnnihilator

@[simp] theorem cokernelDualEquiv_apply
    (φ : Module.Dual K (Cokernel K t j)) (a : Target K t (j + 1)) :
    (cokernelDualEquiv K t j φ).val a =
      φ (Submodule.Quotient.mk a) := rfl

theorem mem_annihilator_iff (φ : Module.Dual K (Target K t (j + 1))) :
    φ ∈ annihilator K t j ↔ ∀ a : Source K t j, φ (presentation a) = 0 := by
  rw [annihilator, Submodule.mem_dualAnnihilator]
  constructor
  · intro h a
    exact h _ ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    exact h a

/-- The coefficient-one monomials span each actual homogeneous component. -/
theorem monomialForms_span :
    Submodule.span K (Set.range (fun e : {e : Fin t →₀ ℕ // e.degree = j} =>
      monomialForm (K := K) e.val e.property)) = ⊤ := by
  apply Submodule.map_injective_of_injective
    (Submodule.injective_subtype (Quartic.Forms K t j))
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  change Submodule.span K (Set.range (fun e : {e : Fin t →₀ ℕ // e.degree = j} =>
    monomial e.val (1 : K))) = Quartic.Forms K t j
  rw [Quartic.Forms, homogeneousSubmodule_eq_finsupp_supported]
  change Submodule.span K _ = MvPolynomial.restrictSupport K {e : Fin t →₀ ℕ | e.degree = j}
  rw [MvPolynomial.restrictSupport_eq_span]
  congr 1
  ext p
  simp

/-- A linear functional is determined by its values on homogeneous monomials. -/
theorem linearForm_eq_zero_of_monomials (f : Module.Dual K (Quartic.Forms K t j))
    (hf : ∀ (e : Fin t →₀ ℕ) (he : e.degree = j), f (monomialForm e he) = 0) :
    f = 0 := by
  have hker : (⊤ : Submodule K (Quartic.Forms K t j)) ≤ f.ker := by
    rw [← monomialForms_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact hf e.val e.property
  apply LinearMap.ext
  intro a
  exact hker Submodule.mem_top

/-- Inserting a homogeneous polynomial in one input column. -/
def columnMap (k : Fin (t + 2)) : Quartic.Forms K t j →ₗ[K] Source K t j :=
  LinearMap.single K (fun _ : Fin (t + 2) => Quartic.Forms K t j) k

/-- Inserting a homogeneous polynomial in one output row. -/
def rowMap (d : Fin 3) : Quartic.Forms K t j →ₗ[K] Target K t j :=
  LinearMap.single K (fun _ : Fin 3 => Quartic.Forms K t j) d

@[simp] theorem columnMap_apply (k : Fin (t + 2)) (a : Quartic.Forms K t j) :
    columnMap k a = Pi.single k a := rfl

@[simp] theorem rowMap_apply (d : Fin 3) (a : Quartic.Forms K t j) :
    rowMap d a = Pi.single d a := rfl

theorem source_eq_sum_columns (a : Source K t j) :
    a = ∑ k : Fin (t + 2), columnMap k (a k) := by
  classical
  ext k
  simp [columnMap, LinearMap.single_apply]

theorem target_eq_sum_rows (a : Target K t j) :
    a = ∑ d : Fin 3, rowMap d (a d) := by
  ext d
  simp [rowMap, LinearMap.single_apply]

theorem mem_annihilator_iff_columns (φ : Module.Dual K (Target K t (j + 1))) :
    φ ∈ annihilator K t j ↔
      ∀ (k : Fin (t + 2)) (a : Quartic.Forms K t j), φ (presentation (columnMap k a)) = 0 := by
  rw [mem_annihilator_iff]
  constructor
  · exact fun h k a => h (columnMap k a)
  · intro h a
    calc
      φ (presentation a) = φ (presentation (∑ k, columnMap k (a k))) :=
        congrArg (fun b => φ (presentation b)) (source_eq_sum_columns a)
      _ = ∑ k, φ (presentation (columnMap k (a k))) := by simp only [map_sum]
      _ = 0 := Finset.sum_eq_zero (fun k _ => h k (a k))

theorem presentation_column_row (k : Fin (t + 2)) (a : Quartic.Forms K t j)
    (d : Fin 3) :
    presentation (columnMap k a) d =
      ∑ i : Fin t, if columnIndex d i = k then variableMul i a else 0 := by
  classical
  rw [presentation_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : columnIndex d i = k <;> simp [h]

theorem presentation_column (k : Fin (t + 2)) (a : Quartic.Forms K t j) :
    presentation (columnMap k a) =
      ∑ d : Fin 3, rowMap d
        (∑ i : Fin t, if columnIndex d i = k then variableMul i a else 0) := by
  rw [target_eq_sum_rows (presentation (columnMap k a))]
  simp only [presentation_column_row]

/-- The transpose recurrence, with coefficients given by evaluations on the
ordinary monomial basis. There are no factorial normalizations. -/
theorem presentation_column_monomial_dual
    (φ : Module.Dual K (Target K t (j + 1))) (k : Fin (t + 2))
    (e : Fin t →₀ ℕ) (he : e.degree = j) :
    φ (presentation (columnMap k (monomialForm e he))) =
      ∑ d : Fin 3, ∑ i : Fin t, if columnIndex d i = k then
        φ (rowMonomial d (e + Finsupp.single i 1) (degree_add_single e he i)) else 0 := by
  classical
  rw [presentation_column]
  simp only [map_sum, apply_ite, map_zero, variableMul_monomialForm]
  rfl

/-- The complete, explicit recurrence criterion for a functional to belong to
the dual of the actual graded convolution cokernel. -/
theorem mem_annihilator_iff_monomial_recurrence
    (φ : Module.Dual K (Target K t (j + 1))) :
    φ ∈ annihilator K t j ↔
      ∀ (k : Fin (t + 2)) (e : Fin t →₀ ℕ) (he : e.degree = j),
        (∑ d : Fin 3, ∑ i : Fin t, if columnIndex d i = k then
          φ (rowMonomial d (e + Finsupp.single i 1) (degree_add_single e he i)) else 0) = 0 := by
  rw [mem_annihilator_iff_columns]
  constructor
  · intro h k e he
    rw [← presentation_column_monomial_dual]
    exact h k (monomialForm e he)
  · intro h k a
    let f : Module.Dual K (Quartic.Forms K t j) :=
      (φ.comp presentation).comp (columnMap k)
    have hf : f = 0 := linearForm_eq_zero_of_monomials f (by
      intro e he
      change φ (presentation (columnMap k (monomialForm e he))) = 0
      rw [presentation_column_monomial_dual]
      exact h k e he)
    exact congrArg (fun g : Module.Dual K (Quartic.Forms K t j) => g a) hf

end

end Quartic.ConvolutionDual
