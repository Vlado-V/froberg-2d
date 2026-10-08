import Quartic.FiniteEndpointNatural

/-! Assemble independently checked finite row chunks without reevaluating the
whole inverse in one Boolean expression. -/
namespace Quartic.FiniteEndpointChunks

/-- Number of chunks of width C needed to cover N rows, for positive C. -/
def chunkCount (N C : ℕ) : ℕ := (N+C-1)/C

theorem index_block_lt {N C i : ℕ} (hC : 0 < C) (hi : i < N) :
    i/C < chunkCount N C := by
  have hdiv := Nat.div_add_mod (N+C-1) C
  rw [Nat.mul_comm C] at hdiv
  have hrem := Nat.mod_lt (N+C-1) hC
  have hbound : N ≤ chunkCount N C*C := by
    unfold chunkCount
    omega
  have hidiv := Nat.div_add_mod i C
  rw [Nat.mul_comm C] at hidiv
  by_contra h
  have hle : chunkCount N C ≤ i/C := by omega
  have hmul := Nat.mul_le_mul_right C hle
  omega

/-- Each row belongs to a checked block at its quotient and remainder indices. -/
theorem forall_lt_of_chunks (P : ℕ → Prop) (N C : ℕ) (hC : 0 < C)
    (hchunks : ∀ k,k < chunkCount N C → ∀ j,j < C → k*C+j < N → P (k*C+j)) :
    ∀ i,i < N → P i := by
  intro i hi
  have hk := index_block_lt hC hi
  have hj := Nat.mod_lt i hC
  have heq := Nat.div_add_mod i C
  rw [Nat.mul_comm C] at heq
  simpa only [heq] using hchunks (i/C) hk (i%C) hj (by omega)

/-- Fin-indexed chunk proofs also supply the natural-index checker interface. -/
theorem forall_lt_of_fin_chunks (P : ℕ → Prop) (N C : ℕ) (hC : 0 < C)
    (hchunks : ∀ k : Fin (chunkCount N C),∀ j : Fin C,
      k.val*C+j.val < N → P (k.val*C+j.val)) : ∀ i,i < N → P i := by
  apply forall_lt_of_chunks P N C hC
  intro k hk j hj hij
  exact hchunks ⟨k,hk⟩ ⟨j,hj⟩ hij

theorem forall_fin_of_chunks (P : ℕ → Prop) (N C : ℕ) (hC : 0 < C)
    (hchunks : ∀ k,k < chunkCount N C → ∀ j,j < C → k*C+j < N → P (k*C+j)) :
    ∀ i : Fin N,P i.val := fun i => forall_lt_of_chunks P N C hC hchunks i.val i.isLt

end Quartic.FiniteEndpointChunks
