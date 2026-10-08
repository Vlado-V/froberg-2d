import Quartic.ConvolutionFactor
import Quartic.ConvolutionDual

/-!
# Ordered-slot polynomials

The exponent in each ordinary slot records a variable index, while the
exponent in the distinguished slot records a target row. This encoding
retains coefficients individually: unlike polarization of a primal form,
it needs no divisions by factorials.
-/

noncomputable section
namespace Quartic.ConvolutionSlots
open MvPolynomial ConvolutionFactor ConvolutionPresentation ConvolutionDual
variable {K : Type*} [Field K] {t j : ℕ}

/-- The separate exponents, before ordinary slots are made symmetric. -/
def slotExponent (d : ℕ) (v : Fin j → ℕ) : Option (Fin j) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun o => o.elim d v)

@[simp] theorem slotExponent_none (d : ℕ) (v : Fin j → ℕ) :
    slotExponent d v none = d := by simp [slotExponent]

@[simp] theorem slotExponent_some (d : ℕ) (v : Fin j → ℕ) (i : Fin j) :
    slotExponent d v (some i) = v i := by simp [slotExponent]

/-- Different row/tuple labels give different monomials. -/
theorem slotExponent_injective : Function.Injective
    (fun a : Fin 3 × (Fin j → Fin t) => slotExponent a.1.val (fun i => (a.2 i).val)) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    simpa using congrArg (fun e => e none) h
  · funext i
    apply Fin.ext
    simpa using congrArg (fun e => e (some i)) h

/-- The polynomial with a prescribed rectangular array of coefficients. -/
def ofCoefficients (c : Fin 3 × (Fin j → Fin t) → K) : Slots K j :=
  ∑ a, monomial (slotExponent a.1.val (fun i => (a.2 i).val)) (c a)

@[simp] theorem coeff_ofCoefficients (c : Fin 3 × (Fin j → Fin t) → K)
    (a : Fin 3 × (Fin j → Fin t)) :
    (ofCoefficients c).coeff (slotExponent a.1.val (fun i => (a.2 i).val)) = c a := by
  classical
  simp only [ofCoefficients, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    rw [ite_eq_right]
    exact fun h => hba (slotExponent_injective h)
  · simp

/-- Encoding an array never loses a coefficient. -/
theorem ofCoefficients_injective : Function.Injective
    (ofCoefficients (K := K) (t := t) (j := j)) := by
  intro c d h
  funext a
  simpa using congrArg (fun p => p.coeff (slotExponent a.1.val (fun i => (a.2 i).val))) h

/-- The distinguished slot has the target's three-row degree bound. -/
theorem ofCoefficients_degree_none (c : Fin 3 × (Fin j → Fin t) → K) :
    (ofCoefficients c).degreeOf none ≤ 2 := by
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro a _
  by_cases h : c a = 0
  · simp [h]
  · rw [degreeOf_monomial_eq _ _ h, slotExponent_none]
    exact Nat.le_of_lt_succ a.1.isLt

/-- Every ordinary slot has the original variable-index degree bound. -/
theorem ofCoefficients_degree_some (c : Fin 3 × (Fin j → Fin t) → K) (i : Fin j) :
    (ofCoefficients c).degreeOf (some i) ≤ t - 1 := by
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro a _
  by_cases h : c a = 0
  · simp [h]
  · rw [degreeOf_monomial_eq _ _ h, slotExponent_some]
    have := (a.2 i).isLt
    omega


/-- Permuting ordinary slots permutes their exponent labels contravariantly. -/
theorem slotExponent_map_perm (d : ℕ) (v : Fin j → ℕ) (σ : Equiv.Perm (Fin j)) :
    (slotExponent d v).mapDomain (Option.map σ) =
      slotExponent d (v ∘ σ.symm) := by
  have hinj : Function.Injective (Option.map σ) := (Equiv.optionCongr σ).injective
  ext o
  obtain ⟨o, rfl⟩ := (Equiv.optionCongr σ).surjective o
  change ((slotExponent d v).mapDomain (Option.map σ)) (Option.map σ o) = _
  rw [Finsupp.mapDomain_apply_of_injective hinj]
  cases o <;> simp [Function.comp_def]

/-- Slot renaming on a rectangular coefficient array. -/
theorem permuteSlots_ofCoefficients
    (c : Fin 3 × (Fin j → Fin t) → K) (σ : Equiv.Perm (Fin j)) :
    permuteSlots σ (ofCoefficients c) =
      ofCoefficients (fun a => c (a.1, a.2 ∘ σ)) := by
  classical
  simp only [permuteSlots, ofCoefficients, map_sum, rename_monomial,
    slotExponent_map_perm]
  let e : (Fin 3 × (Fin j → Fin t)) ≃ (Fin 3 × (Fin j → Fin t)) :=
    (Equiv.refl (Fin 3)).prodCongr (Equiv.arrowCongr σ.symm (Equiv.refl (Fin t)))
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro a _
  simp [e, Function.comp_def, Prod.map_def]
  rfl


/-- Identifying the distinguished slot with an ordinary one adds their exponents. -/
theorem slotExponent_map_diagonal (d : ℕ) (v : Fin j → ℕ) (i : Fin j) :
    (slotExponent d v).mapDomain (fun o => o.elim i id) =
      Finsupp.single i d + Finsupp.equivFunOnFinite.symm v := by
  classical
  ext k
  rw [Finsupp.mapDomain_apply, Finsupp.sum_fintype]
  · rw [Fintype.sum_option]
    dsimp only [Option.elim, id]
    simp [slotExponent, Finsupp.single_apply]
  · intro a
    simp

/-- The merged exponents with the remaining slots retained separately. -/
def mergedExponent (slot : Fin (j + 1)) (k : ℕ) (v : Fin j → ℕ) :
    Fin (j + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (slot.insertNth k v)

theorem map_diagonal_insertNth (d h : ℕ) (v : Fin j → ℕ) (slot : Fin (j + 1)) :
    (slotExponent d (slot.insertNth h v)).mapDomain (fun o => o.elim slot id) =
      mergedExponent slot (h + d) v := by
  rw [slotExponent_map_diagonal]
  ext k
  obtain rfl | ⟨l, rfl⟩ := slot.eq_self_or_eq_succAbove k
  · simp [mergedExponent, add_comm]
  · simp [mergedExponent, Finsupp.single_eq_of_ne, Fin.succAbove_ne]

/-- Grouping row and variable indices according to their sum. -/
theorem sum_monomial_columns {σ : Type*} (E : Fin (t + 2) → σ →₀ ℕ)
    (c : Fin 3 → Fin t → K) :
    (∑ d : Fin 3, ∑ i : Fin t, monomial (E (columnIndex d i)) (c d i)) =
      ∑ k : Fin (t + 2), monomial (E k)
        (∑ d : Fin 3, ∑ i : Fin t, if columnIndex d i = k then c d i else 0) := by
  classical
  symm
  simp only [map_sum, apply_ite, map_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  simp

/-- The source-column recurrence implies diagonal vanishing for an arbitrary slot. -/
theorem ofCoefficients_diagonal_zero
    (c : Fin 3 × (Fin (j + 1) → Fin t) → K) (slot : Fin (j + 1))
    (hc : ∀ (v : Fin j → Fin t) (k : Fin (t + 2)),
      (∑ d : Fin 3, ∑ i : Fin t, if columnIndex d i = k then
        c (d, slot.insertNth i v) else 0) = 0) :
    diagonalMap K (j + 1) slot (ofCoefficients c) = 0 := by
  classical
  rw [ofCoefficients, map_sum, Fintype.sum_prod_type]
  simp only [diagonalMap, rename_monomial]
  have hi (d : Fin 3) :
      (∑ v : Fin (j + 1) → Fin t,
        monomial ((slotExponent d.val (fun l => (v l).val)).mapDomain
          (fun o => o.elim slot id)) (c (d, v))) =
      ∑ i : Fin t, ∑ v : Fin j → Fin t,
        monomial (mergedExponent slot (columnIndex d i).val (fun l => (v l).val))
          (c (d, slot.insertNth i v)) := by
    rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ => Fin t) slot)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro v _
    have hv : (fun l => ((Fin.insertNthEquiv (fun _ => Fin t) slot) (i, v) l).val) =
        slot.insertNth i.val (fun l => (v l).val) := by
      funext l
      obtain rfl | ⟨a, rfl⟩ := slot.eq_self_or_eq_succAbove l <;> simp
    rw [hv, map_diagonal_insertNth]
    rfl
  simp_rw [hi]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i : Fin t => fun v : Fin j → Fin t => _)]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  rw [sum_monomial_columns (fun k : Fin (t + 2) =>
    mergedExponent slot k.val (fun l => (v l).val))
    (fun d i => c (d, slot.insertNth i v))]
  simp [hc]

end Quartic.ConvolutionSlots
