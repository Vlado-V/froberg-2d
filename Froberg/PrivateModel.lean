import Froberg.PrivateQuotients

/-! A common private-column model has full spark, mixed position, and all
polynomial injection bounds required through the endpoint degree. -/
noncomputable section
namespace Froberg.PrivateColumns
open OuterInjection

lemma private_small_fiber_bound {k s h : ℕ} (hk : 0 < k) (hs : 2 ≤ s)
    (hh : h=k*(2*s+1).choose s) : k*(s+1)+2 ≤ h := by
  have hm := Nat.choose_le_middle 1 (2*s+1)
  rw [Nat.choose_one_right,show (2*s+1)/2=s by omega] at hm
  rw [hh]
  nlinarith

lemma exists_generic_private_vectors {K : Type*} [Field K] [Infinite K]
    (k a s b h : ℕ) :
    ∃ u : Labels k a s ⊕ Fin b → Fin h → K,
      (∀ U : Finset (Labels k a s ⊕ Fin b),U.card ≤ h → LinearIndependent K (fun i : U => u i.val)) ∧
      MixedExterior.UniversalMixedPosition u ∧
      (∀ U : Finset (Labels k a s),U.card ≤ h → LinearIndependent K (fun i : U => u (Sum.inl i.val))) ∧
      MixedExterior.UniversalMixedPosition (fun i => u (Sum.inl i)) := by
  classical
  obtain ⟨u,hu,hm⟩ := MixedExterior.exists_universal_mixed_vectors
    (K := K) (α := Labels k a s ⊕ Fin b) h
  exact ⟨u,hu,hm,MixedExterior.full_spark_comp u hu Function.Embedding.inl,
    hm.comp Function.Embedding.inl⟩

end Froberg.PrivateColumns
