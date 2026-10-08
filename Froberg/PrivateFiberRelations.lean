import Froberg.PrivatePairTargets

/-! Coefficientwise kernel calculation for the fixed private columns. Every
relation is supported on pairwise private powers, with one equation per pair. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PrivateColumns
open Finset
variable {K V T : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup T] [Module K T]
  {a z s b : ℕ}

/-- The literal target coefficient obtained by multiplying each coefficient
array by its private monomial and applying its output map. -/
def privateCoefficient (ι : Fin b ↪ Fin z) (A : Fin b → V →ₗ[K] T)
    (v : Fin b → (Fin (a+z) →₀ ℕ) → V) (β : Fin (a+z) →₀ ℕ) : T :=
  ∑ i, if privateExponent a s ι i ≤ β then A i (v i (β-privateExponent a s ι i)) else 0

/-- A coefficient away from the pairwise private powers has a unique output
column, hence it vanishes in any relation. Diagonal private coefficients are
included in this assertion. -/
theorem private_relation_support (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (A : Fin b → V →ₗ[K] T) (hA : ∀ i, Function.Injective (A i))
    (v : Fin b → (Fin (a+z) →₀ ℕ) → V)
    (hv : ∀ β, β.degree=2*s → privateCoefficient (s := s) ι A v β=0)
    (i : Fin b) (α : Fin (a+z) →₀ ℕ) (hα : α.degree=s)
    (hprivate : ∀ j, i ≠ j → α ≠ privateExponent a s ι j) : v i α=0 := by
  classical
  let β := privateExponent a s ι i+α
  have hβ : β.degree=2*s := by simp only [β,map_add,privateExponent_degree,hα]; omega
  have h := hv β hβ
  have he : privateCoefficient (s := s) ι A v β=A i (v i α) := by
    unfold privateCoefficient
    rw [Finset.sum_eq_single i]
    · rw [if_pos (show privateExponent a s ι i ≤ β from le_add_right le_rfl)]
      simp only [β,add_tsub_cancel_left]
    · intro j _ hji
      rw [if_neg]
      intro hj
      exact hprivate j (Ne.symm hji) (private_overlap_coefficient ι (Ne.symm hji) hα hj)
    · intro hi
      exact False.elim (hi (mem_univ i))
  rw [he] at h
  exact hA i (h.trans (map_zero _).symm)

/-- Each off-diagonal private overlap satisfies precisely its two-column
output equation, with no contributions from other columns. -/
theorem private_relation_pair (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (A : Fin b → V →ₗ[K] T) (v : Fin b → (Fin (a+z) →₀ ℕ) → V)
    (hv : ∀ β, β.degree=2*s → privateCoefficient (s := s) ι A v β=0)
    (i j : Fin b) (hij : i ≠ j) :
    A i (v i (privateExponent a s ι j)) + A j (v j (privateExponent a s ι i))=0 := by
  classical
  let β := privateExponent a s ι i+privateExponent a s ι j
  have hβ : β.degree=2*s := by simp only [β,map_add,privateExponent_degree]; omega
  have h := hv β hβ
  have he : privateCoefficient (s := s) ι A v β =
      A i (v i (privateExponent a s ι j)) + A j (v j (privateExponent a s ι i)) := by
    unfold privateCoefficient
    rw [← Finset.sum_subset (show ({i,j} : Finset (Fin b)) ⊆ univ from subset_univ _) (by
      intro k _ hk
      rw [if_neg]
      intro hdiv
      have hk' := (private_pair_divisors hs ι i j k).mp hdiv
      exact hk (by simpa using hk'))]
    rw [Finset.sum_insert (show i ∉ ({j} : Finset (Fin b)) by simpa using hij),Finset.sum_singleton]
    rw [if_pos (le_add_right le_rfl),if_pos (le_add_left le_rfl)]
    simp only [β,add_tsub_cancel_left,add_tsub_cancel_right]
  exact he.symm.trans h

end Froberg.PrivateColumns
