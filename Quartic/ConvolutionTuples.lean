import Quartic.ConvolutionDual
import Mathlib.Data.Finsupp.Order

/-!
# Ordered tuples and homogeneous monomial exponents

An ordered tuple records a monomial by summing its variable exponents. Every
homogeneous monomial has such a tuple, and permuting the slots preserves the
exponent. These facts connect the actual polynomial dual to symmetric-slot
coordinate encodings.
-/

namespace Quartic.ConvolutionTuples

noncomputable section

open Quartic.ConvolutionPresentation Quartic.ConvolutionDual

variable {t j : ℕ}

/-- The exponent multiset underlying an ordered tuple of variable indices. -/
def tupleExponent (v : Fin j → Fin t) : Fin t →₀ ℕ :=
  ∑ k : Fin j, Finsupp.single (v k) 1

@[simp] theorem tupleExponent_degree (v : Fin j → Fin t) :
    (tupleExponent v).degree = j := by
  simp [tupleExponent]

@[simp] theorem tupleExponent_cons (i : Fin t) (v : Fin j → Fin t) :
    tupleExponent (Fin.cons i v) = Finsupp.single i 1 + tupleExponent v := by
  simp [tupleExponent, Fin.sum_univ_succ]

@[simp] theorem tupleExponent_insertNth (slot : Fin (j + 1)) (i : Fin t)
    (v : Fin j → Fin t) :
    tupleExponent (slot.insertNth i v) = Finsupp.single i 1 + tupleExponent v := by
  unfold tupleExponent
  rw [Fin.sum_univ_succAbove _ slot]
  simp

/-- The exponent is unchanged under arbitrary permutations of the slots. -/
theorem tupleExponent_perm (v : Fin j → Fin t) (σ : Equiv.Perm (Fin j)) :
    tupleExponent (v ∘ σ) = tupleExponent v := by
  unfold tupleExponent
  exact Equiv.sum_comp σ (fun k => Finsupp.single (v k) 1)

/-- Every degree-`j` monomial exponent can be listed as a `j`-tuple. -/
theorem exists_tupleExponent (e : Fin t →₀ ℕ) (he : e.degree = j) :
    ∃ v : Fin j → Fin t, tupleExponent v = e := by
  classical
  induction j generalizing e with
  | zero =>
    have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp he
    exact ⟨Fin.elim0, by simp [tupleExponent, he0]⟩
  | succ j ih =>
    obtain ⟨i, hi⟩ : e.support.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      have he0 : e = 0 := Finsupp.support_eq_empty.mp hempty
      simp [he0] at he
    have hle : Finsupp.single i 1 ≤ e := by
      simpa [Nat.one_le_iff_ne_zero] using hi
    obtain ⟨f, hf⟩ := le_iff_exists_add.mp hle
    have hfdegree : f.degree = j := by
      have h := congrArg Finsupp.degree hf
      simp only [map_add, Finsupp.degree_single] at h
      omega
    obtain ⟨v, hv⟩ := ih f hfdegree
    exact ⟨Fin.cons i v, by rw [tupleExponent_cons, hv, ← hf]⟩

section Functionals

variable {K : Type*} [Field K]

/-- A homogeneous functional vanishes when all its ordered-tuple monomial
coefficients vanish. -/
theorem linearForm_eq_zero_of_tuple_monomials
    (f : Module.Dual K (Quartic.Forms K t j))
    (hf : ∀ v : Fin j → Fin t,
      f (monomialForm (tupleExponent v) (tupleExponent_degree v)) = 0) : f = 0 := by
  apply linearForm_eq_zero_of_monomials
  intro e he
  obtain ⟨v, rfl⟩ := exists_tupleExponent e he
  exact hf v

/-- A target functional is determined by its values on all row monomials. -/
theorem target_linearForm_eq_zero_of_rowMonomials
    (φ : Module.Dual K (Target K t j))
    (hφ : ∀ (d : Fin 3) (e : Fin t →₀ ℕ) (he : e.degree = j),
      φ (rowMonomial d e he) = 0) : φ = 0 := by
  have hrow (d : Fin 3) : φ.comp (rowMap d) = 0 := by
    apply linearForm_eq_zero_of_monomials
    intro e he
    exact hφ d e he
  apply LinearMap.ext
  intro a
  calc
    φ a = φ (∑ d : Fin 3, rowMap d (a d)) := congrArg φ (target_eq_sum_rows a)
    _ = ∑ d : Fin 3, φ (rowMap d (a d)) := by simp only [map_sum]
    _ = 0 := Finset.sum_eq_zero (fun d _ =>
      congrArg (fun f : Module.Dual K (Quartic.Forms K t j) => f (a d)) (hrow d))

/-- Ordered tuple coordinates detect every target functional. -/
theorem target_linearForm_eq_zero_of_tuple_rowMonomials
    (φ : Module.Dual K (Target K t j))
    (hφ : ∀ (d : Fin 3) (v : Fin j → Fin t),
      φ (rowMonomial d (tupleExponent v) (tupleExponent_degree v)) = 0) : φ = 0 := by
  apply target_linearForm_eq_zero_of_rowMonomials
  intro d e he
  obtain ⟨v, rfl⟩ := exists_tupleExponent e he
  exact hφ d v

/-- Extensionality in ordinary row-monomial coordinates. -/
theorem target_linearForm_ext (φ ψ : Module.Dual K (Target K t j))
    (h : ∀ (d : Fin 3) (e : Fin t →₀ ℕ) (he : e.degree = j),
      φ (rowMonomial d e he) = ψ (rowMonomial d e he)) : φ = ψ := by
  apply sub_eq_zero.mp
  apply target_linearForm_eq_zero_of_rowMonomials
  intro d e he
  exact sub_eq_zero.mpr (h d e he)

/-- Extensionality in ordered tuple row-monomial coordinates. -/
theorem target_linearForm_ext_tuple (φ ψ : Module.Dual K (Target K t j))
    (h : ∀ (d : Fin 3) (v : Fin j → Fin t),
      φ (rowMonomial d (tupleExponent v) (tupleExponent_degree v)) =
      ψ (rowMonomial d (tupleExponent v) (tupleExponent_degree v))) : φ = ψ := by
  apply sub_eq_zero.mp
  apply target_linearForm_eq_zero_of_tuple_rowMonomials
  intro d v
  exact sub_eq_zero.mpr (h d v)

end Functionals

end

end Quartic.ConvolutionTuples
