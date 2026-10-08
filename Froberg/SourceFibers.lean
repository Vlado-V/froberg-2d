import Froberg.FiberDimensions

/-! Exact source-fiber dimensions in the core-attached outer quotient. -/
noncomputable section
namespace Froberg.OuterInjection
open Module

theorem corePart_degree_le {a z : ℕ} (β : Fin (a + z) →₀ ℕ) :
    (corePart β).degree ≤ β.degree :=
  Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd (Fin.castAdd_injective a z).injOn

theorem embedded_corePart_le {a z : ℕ} (β : Fin (a + z) →₀ ℕ) :
    (corePart β).mapDomain (Fin.castAdd z) ≤ β := by
  intro j
  by_cases hj : j ∈ Set.range (Fin.castAdd z : Fin a → Fin (a + z))
  · obtain ⟨i, rfl⟩ := hj
    rw [Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective a z), corePart_apply]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hj]
    exact Nat.zero_le _

/-- A degree-s monomial has exactly k attached labels if it lies wholly in the
core, and no labels if it uses a free variable. -/
theorem card_source_labels {k a z s : ℕ} (β : Fin (a + z) →₀ ℕ) (hβ : β.degree = s) :
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} =
      if (corePart β).degree = s then k else 0 := by
  classical
  have hupper := card_target_labels_le_core (k := k) (s := s) z β
  have hdegree : (corePart β).degree ≤ s := hβ ▸ corePart_degree_le β
  split_ifs with hcore
  · rw [hcore, Nat.choose_self, mul_one] at hupper
    let m : Sym (Fin a) s := (exponentEquiv a s).symm ⟨corePart β, hcore⟩
    have hm : (exponentEquiv a s m).val = corePart β := by
      exact congrArg Subtype.val ((exponentEquiv a s).apply_symm_apply ⟨corePart β, hcore⟩)
    let f : Fin k → {i : Labels k a s // coreExponent z i ≤ β} := fun t =>
      ⟨(t, m), by
        change ((exponentEquiv a s m).val).mapDomain (Fin.castAdd z) ≤ β
        rw [hm]
        exact embedded_corePart_le β⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact congrArg (fun p : {i : Labels k a s // coreExponent z i ≤ β} => p.val.1) hij
    have hlower : k ≤ Fintype.card {i : Labels k a s // coreExponent z i ≤ β} := by
      simpa using Fintype.card_le_of_injective f hf
    exact Nat.le_antisymm hupper hlower
  · have hlt : (corePart β).degree < s := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, mul_zero] at hupper
    exact Nat.eq_zero_of_le_zero hupper

theorem source_quotientFiber_finrank {K : Type*} [Field K] {k a z s h : ℕ}
    (v : Labels k a s → Fin h → K) (β : Fin (a + z) →₀ ℕ) (hβ : β.degree = s)
    (hi : LinearIndependent K (fun i : {i : Labels k a s // coreExponent z i ≤ β} => v i.val)) :
    finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β) =
      if (corePart β).degree = s then h - k else h := by
  rw [AttachedMultiplication.quotientFiber_finrank _ _ β hi, Fintype.card_fin,
    card_source_labels β hβ]
  split_ifs <;> simp

/-- General-position attaching vectors give the exact source capacities. -/
theorem source_quotientFiber_finrank_of_general_position {K : Type*} [Field K]
    {k a z s h : ℕ} (hk : k ≤ h) (v : Labels k a s → Fin h → K)
    (hv : ∀ T : Finset (Labels k a s), T.card ≤ h → LinearIndependent K (fun i : T => v i.val))
    (β : Fin (a + z) →₀ ℕ) (hβ : β.degree = s) :
    finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β) =
      if (corePart β).degree = s then h - k else h := by
  classical
  apply source_quotientFiber_finrank v β hβ
  let T : Finset (Labels k a s) := Finset.univ.filter (fun i => coreExponent z i ≤ β)
  have hT : T.card ≤ h := by
    have hc := card_source_labels (k := k) β hβ
    have hcard : T.card = Fintype.card {i : Labels k a s // coreExponent z i ≤ β} := by
      simp only [T, Fintype.card_subtype]
    rw [hcard, hc]
    split_ifs <;> omega
  let f : {i : Labels k a s // coreExponent z i ≤ β} → T := fun i =>
    ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.property⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg (fun t : T => t.val) hij)
  exact (hv T hT).comp f hf

end Froberg.OuterInjection
