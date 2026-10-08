import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! A bounded disjoint exceptional family has a bounded hitting set. -/
namespace Froberg.ExceptionalFamilies

variable {α T : Type*} [DecidableEq α] [DecidableEq T]

/-- The combinatorial step turning a uniform bound on pairwise disjoint failures
into a bounded collection of labels meeting every failure. -/
theorem exists_hitting_set (sets : T → Finset α) (E : Finset T) (h q : ℕ)
    (hsize : ∀ t ∈ E, (sets t).card ≤ h)
    (hne : ∀ t ∈ E, (sets t).Nonempty)
    (hpack : ∀ B : Finset T, B ⊆ E →
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (sets i) (sets j)) → B.card ≤ q) :
    ∃ U : Finset α, U.card ≤ h*q ∧ ∀ t ∈ E, ∃ a ∈ U, a ∈ sets t := by
  classical
  let candidates : Finset (Finset T) := E.powerset.filter (fun B =>
    ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (sets i) (sets j))
  have hcan : candidates.Nonempty := ⟨∅,by simp [candidates]⟩
  obtain ⟨B,hB,hmax⟩ := Finset.exists_max_image candidates Finset.card hcan
  have hBE : B ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  have hpair : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (sets i) (sets j) :=
    (Finset.mem_filter.mp hB).2
  refine ⟨B.biUnion sets,?_,?_⟩
  · calc
      (B.biUnion sets).card ≤ B.card*h :=
        Finset.card_biUnion_le_card_mul B sets h (fun i hi => hsize i (hBE hi))
      _ ≤ q*h := Nat.mul_le_mul_right h (hpack B hBE hpair)
      _ = h*q := Nat.mul_comm q h
  · intro t ht
    by_contra hn
    have hdis : ∀ i ∈ B, Disjoint (sets t) (sets i) := by
      intro i hi
      apply Finset.disjoint_left.mpr
      intro a hat hai
      exact hn ⟨a,Finset.mem_biUnion.mpr ⟨i,hi,hai⟩,hat⟩
    have htB : t ∉ B := by
      intro htB
      obtain ⟨a,ha⟩ := hne t ht
      exact Finset.disjoint_left.mp (hdis t htB) ha ha
    have hsub : insert t B ⊆ E := Finset.insert_subset_iff.mpr ⟨ht,hBE⟩
    have hp : ∀ i ∈ insert t B, ∀ j ∈ insert t B,
        i ≠ j → Disjoint (sets i) (sets j) := by
      intro i hi j hj hij
      rcases Finset.mem_insert.mp hi with rfl | hiB
      · rcases Finset.mem_insert.mp hj with rfl | hjB
        · exact (hij rfl).elim
        · exact hdis j hjB
      · rcases Finset.mem_insert.mp hj with rfl | hjB
        · exact (hdis i hiB).symm
        · exact hpair i hiB j hjB hij
    have hic : insert t B ∈ candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub,hp⟩
    have hm := hmax (insert t B) hic
    rw [Finset.card_insert_of_notMem htB] at hm
    omega

end Froberg.ExceptionalFamilies
