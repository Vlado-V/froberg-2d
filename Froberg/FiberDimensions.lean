import Froberg.AttachedFibers
import Froberg.CoreDivisors

/-! Exact dimensions of the vector fibers of the attached-monomial quotient. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] {n : ℕ}

theorem relationFiber_finrank (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (β : Fin n →₀ ℕ) (hi : LinearIndependent K (fun i : {i // e i ≤ β} => v i.val)) :
    finrank K (relationFiber e v β) = Fintype.card {i // e i ≤ β} := by
  exact finrank_span_eq_card hi

theorem quotientFiber_finrank (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (β : Fin n →₀ ℕ) (hi : LinearIndependent K (fun i : {i // e i ≤ β} => v i.val)) :
    finrank K ((J → K) ⧸ relationFiber e v β) =
      Fintype.card J - Fintype.card {i // e i ≤ β} := by
  rw [Submodule.finrank_quotient, relationFiber_finrank e v β hi]
  simp

/-- In the actual core-attached model, the coarse capacity is a lower bound for
its exact vector-quotient dimension. -/
theorem core_quotientFiber_capacity {k a z s h : ℕ}
    (v : OuterInjection.Labels k a s → Fin h → K) (β : Fin (a+z) →₀ ℕ)
    (hi : LinearIndependent K
      (fun i : {i : OuterInjection.Labels k a s // OuterInjection.coreExponent z i ≤ β} => v i.val)) :
    h - k * (OuterInjection.corePart β).degree.choose s ≤
      finrank K ((Fin h → K) ⧸ relationFiber (OuterInjection.coreExponent z) v β) := by
  rw [quotientFiber_finrank _ _ β hi, Fintype.card_fin]
  exact Nat.sub_le_sub_left (OuterInjection.card_target_labels_le_core z β) h

end Froberg.AttachedMultiplication
