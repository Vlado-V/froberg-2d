module

public import Froberg.OuterInjection

@[expose] public section

/-! Divisor counts using the actual core degree, rather than total degree. -/
noncomputable section
namespace Froberg.OuterInjection

/-- Restrict an exponent vector to the core variables. -/
def corePart {a z : ℕ} (β : Fin (a+z) →₀ ℕ) : Fin a →₀ ℕ :=
  β.comapDomain (Fin.castAdd z) (Fin.castAdd_injective a z).injOn

@[simp] theorem corePart_apply {a z : ℕ} (β : Fin (a+z) →₀ ℕ) (i : Fin a) :
    corePart β i = β (Fin.castAdd z i) := rfl

theorem core_divisor_le {k a z s : ℕ} (β : Fin (a+z) →₀ ℕ) (i : Labels k a s)
    (hi : coreExponent z i ≤ β) : (exponentEquiv a s i.2).val ≤ corePart β := by
  intro j
  have h := hi (Fin.castAdd z j)
  simpa only [coreExponent, Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective a z),
    corePart_apply] using h

/-- The exact core-degree bound used for the coarse target capacities. -/
theorem card_target_labels_le_core {k a s : ℕ} (z : ℕ) (β : Fin (a+z) →₀ ℕ) :
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} ≤
      k * (corePart β).degree.choose s := by
  classical
  let f : {i : Labels k a s // coreExponent z i ≤ β} →
      Fin k × MonomialExpansion.Divisor (corePart β) s := fun i =>
    (i.val.1,⟨(exponentEquiv a s i.val.2).val,
      Finset.mem_filter.mpr ⟨MonomialExpansion.mem_exponents.mpr
        (exponentEquiv a s i.val.2).property,core_divisor_le β i.val i.property⟩⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p : Fin k × MonomialExpansion.Divisor (corePart β) s => p.1) hij
    · apply (exponentEquiv a s).injective
      apply Subtype.ext
      exact congrArg (fun p : Fin k × MonomialExpansion.Divisor (corePart β) s => p.2.val) hij
  calc
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} ≤
        Fintype.card (Fin k × MonomialExpansion.Divisor (corePart β) s) :=
      Fintype.card_le_of_injective f hf
    _ = k * Fintype.card (MonomialExpansion.Divisor (corePart β) s) := by simp
    _ ≤ k * (corePart β).degree.choose s := Nat.mul_le_mul_left k
      (MonomialExpansion.card_divisor_le (corePart β) s)

end Froberg.OuterInjection
