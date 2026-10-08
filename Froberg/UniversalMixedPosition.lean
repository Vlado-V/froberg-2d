import Froberg.CommonMixedMinors

/-! A single generic vector family satisfies all disjoint mixed-minor conditions. -/
noncomputable section
namespace Froberg.MixedExterior

abbrev MixedConfiguration (h : ℕ) (α : Type*) :=
  Σ r : Fin (h+1),
    Σ t : Set.powersetCard (Fin (r.val+(h-r.val))) r.val → Fin ((h-r.val)+1),
      ((Σ I, Fin (t I).val) ↪ α)

variable {K α : Type*} [Field K] [Fintype α] [DecidableEq α]

/-- Every possible exterior degree, every size of added-vector block, and every
pairwise disjoint assignment of its labels satisfies the actual mixed determinant condition. -/
def UniversalMixedPosition {h : ℕ} (v : α → Fin h → K) : Prop :=
  ∀ c : MixedConfiguration h α,
    Matrix.det (fun I J => mixedRow
      (paddedVectors (fun I => (c.2.1 I).val) c.2.2
        (fun a j => v a (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ c.1.isLt)) j)) I) J) ≠ 0

/-- Finite simultaneous nonvanishing gives full spark and the uniform mixed-minor
condition on one and the same vector family. -/
theorem exists_universal_mixed_vectors [Infinite K] (h : ℕ) :
    ∃ v : α → Fin h → K,
      (∀ S : Finset α, S.card ≤ h → LinearIndependent K (fun i : S => v i.val)) ∧
      UniversalMixedPosition v := by
  classical
  let r : MixedConfiguration h α → ℕ := fun c => c.1.val
  let l : MixedConfiguration h α → ℕ := fun c => h-c.1.val
  have hr : ∀ c, r c+l c=h := fun c => Nat.add_sub_of_le (Nat.le_of_lt_succ c.1.isLt)
  obtain ⟨v,hv,hm⟩ := exists_common_mixed_vectors (K := K) h r l hr
    (fun c I => (c.2.1 I).val) (fun c I => Nat.le_of_lt_succ (c.2.1 I).isLt)
    (fun c => c.2.2)
  exact ⟨v,hv,hm⟩

end Froberg.MixedExterior
