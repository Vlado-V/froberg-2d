module

public import Froberg.UniversalMixedPosition
public import Froberg.OuterInjection

@[expose] public section

/-! One actual outer presentation has both full rank and uniform mixed position. -/
noncomputable section
namespace Froberg.OuterInjection

/-- Full spark of the attached vectors gives injectivity in every degree up to
an explicit divisor-count threshold. -/
theorem injective_attached_of_full_spark {K : Type*} [Field K]
    {k a z s d h : ℕ} (v : Labels k a s → Fin h → K)
    (hv : ∀ S : Finset (Labels k a s), S.card ≤ h →
      LinearIndependent K (fun i : S => v i.val))
    (hh : k * (s+d).choose s ≤ h) :
    ∀ c ≤ d, Function.Injective
      (AttachedMultiplication.multiplication (d := c) (coreExponent z) v) := by
  classical
  intro c hc
  apply AttachedMultiplication.injective_of_independent_fibers (coreExponent z) v
    (coreExponent_degree z)
  intro β hβ
  let U : Finset (Labels k a s) := Finset.univ.filter (fun i => coreExponent z i ≤ β)
  have hU : U.card ≤ h := by
    have hcard : Fintype.card {i : Labels k a s // coreExponent z i ≤ β} ≤ h :=
      (card_target_labels_le (k := k) (s := s) z β).trans (by
        rw [hβ]
        exact (Nat.mul_le_mul_left k (Nat.choose_le_choose s (Nat.add_le_add_left hc s))).trans hh)
    simpa only [Fintype.card_subtype] using hcard
  let f : {i : Labels k a s // coreExponent z i ≤ β} → U := fun i =>
    ⟨i.val,by simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]; exact i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg (fun x : U => x.val) hij)
  exact (hv U hU).comp f hf

/-- Generic specialization simultaneously satisfies the actual polynomial
injectivity and all uniform mixed-minor conditions. -/
theorem exists_generic_outer_vectors {K : Type*} [Field K] [Infinite K]
    (k a z s d h : ℕ) (hh : k * (s+d).choose s ≤ h) :
    ∃ v : Labels k a s → Fin h → K,
      (∀ S : Finset (Labels k a s), S.card ≤ h →
        LinearIndependent K (fun i : S => v i.val)) ∧
      MixedExterior.UniversalMixedPosition v ∧
      ∀ c ≤ d, Function.Injective
        (AttachedMultiplication.multiplication (d := c) (coreExponent z) v) := by
  classical
  obtain ⟨v,hv,hm⟩ := MixedExterior.exists_universal_mixed_vectors
    (K := K) (α := Labels k a s) h
  exact ⟨v,hv,hm,injective_attached_of_full_spark v hv hh⟩

end Froberg.OuterInjection
