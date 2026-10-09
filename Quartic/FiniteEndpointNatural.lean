module

public import Quartic.FiniteEndpointCertificate

@[expose] public section

/-! Compact natural-index sparse certificates, with explicit bounds proving that
no modular wraparound changes their matrix entries. -/
namespace Quartic.FiniteEndpointNatural
open FiniteEndpointChecker FiniteEndpointCertificate

variable {N : ℕ}

def finRows (hN : 0 < N) (A : ℕ → List ℕ) (i : Fin N) : List (Fin N) :=
  (A i.val).map (fun j => ⟨j % N,Nat.mod_lt j hN⟩)

def finInverse (B : ℕ → ℕ) (i : Fin N) : ℕ := B i.val

/-- Bounded natural indices preserve the literal sparse inverse row equation. -/
theorem inverse_row_eq (hN : 0 < N) (A : ℕ → List ℕ) (B : ℕ → ℕ)
    (i : Fin N) (hbound : ∀ j ∈ A i.val,j < N) :
    ((finRows hN A i).map (finInverse B)) = (A i.val).map B := by
  simp only [finRows,finInverse,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j hj
  rw [Nat.mod_eq_of_lt (hbound j hj)]

/-- Individual, independently checked natural-index rows certify the Fin matrix. -/
theorem checkInverse_of_natural_equations (hN : 0 < N) (A : ℕ → List ℕ) (B : ℕ → ℕ)
    (hbound : ∀ i : Fin N,∀ j ∈ A i.val,j < N)
    (hrow : ∀ i : Fin N,xorSum ((A i.val).map B) = 2^i.val) :
    checkInverse (finRows hN A) (finInverse B) = true := by
  apply checkInverse_of_equations
  intro i
  rw [inverse_row_eq hN A B i (hbound i)]
  exact hrow i

/-- Natural-index enumeration can also be checked without introducing Fin proof terms. -/
theorem checkInverse_of_bounded_equations (hN : 0 < N) (A : ℕ → List ℕ) (B : ℕ → ℕ)
    (hbound : ∀ i < N,∀ j ∈ A i,j < N)
    (hrow : ∀ i < N,xorSum ((A i).map B) = 2^i) :
    checkInverse (finRows hN A) (finInverse B) = true :=
  checkInverse_of_natural_equations hN A B (fun i => hbound i.val i.isLt)
    (fun i => hrow i.val i.isLt)

end Quartic.FiniteEndpointNatural
