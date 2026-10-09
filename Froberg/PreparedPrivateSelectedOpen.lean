module

public import Froberg.PreparedPrivateKernels

@[expose] public section

/-! Exact first and later row witnesses select one prepared family with
all ordinary rows and all private separations simultaneously. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_common_open_of_row_witnesses [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (h2 : 2∈J)
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (hfirst : ∃ p : Space n d q J counts O,
      (privateAugmentedRow hO ⟨2,h2⟩ p (fun i => (P i).val)).ker=
        ((rowConstants hO ⟨2,h2⟩ p).prodMap (intrinsicPrivateBoundary P)).range)
    (hlater : ∀ R : J,R.val≠2 → ∃ p : Space n d q J counts O,
      (privateAugmentedRow hO R p (fun i => (P i).val)).ker=
        (privateAugmentedConstants (b := b) hO R p).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        (∀ R : J,(privateAugmentedRow hO R p (fun i => (P i).val)).ker=
          ((rowConstants hO R p).prodMap (privateBoundaryAt P R.val)).range) ∧
        (∀ R : J,(row hO R p).ker=(rowConstants hO R p).range) ∧
        (∀ R : J,R.val≠2 → ∀ x u,
          row hO R p x+privateRowMap (d := d) (fun i => (P i).val) R.val u=0 → u=0) := by
  have hwitness : ∀ R : J,∃ p : Space n d q J counts O,
      (privateAugmentedRow hO R p (fun i => (P i).val)).ker=
        ((rowConstants hO R p).prodMap (privateBoundaryAt P R.val)).range := by
    intro R
    by_cases hR : R.val=2
    · have hReq : R=⟨2,h2⟩ := Subtype.ext hR
      subst R
      simpa only [privateBoundaryAt_two] using hfirst
    · obtain ⟨p,hp⟩ := hlater R hR
      refine ⟨p,?_⟩
      rw [privateBoundaryAt_ne P hR,range_prodMap_zero_eq_inl]
      exact hp
  obtain ⟨D,hD,hgood⟩ := private_rows_common_open hO hJ (fun i => (P i).val)
    (fun _ => Fin b → Fin b → K) (fun R => privateBoundaryAt P R.val)
    (fun R => privateBoundaryAt_cycle P R.val) hwitness
  refine ⟨D,hD,?_⟩
  intro p hp
  have hh := hgood p hp
  exact ⟨hh,fun R => private_row_ordinary_exact hO R p P (hh R),
    fun R hR => private_row_separated hO R hR p P (hh R)⟩

end Froberg.PreparedParameters
