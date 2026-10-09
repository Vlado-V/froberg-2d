module

public import Froberg.PreparedPrivateBoundaryOpen

@[expose] public section

/-! All private rows are exact on one common coefficient open. The private
polynomial tuple is fixed once before the row opens are intersected. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_rows_common_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (B : J → Type*) [∀ R,AddCommGroup (B R)] [∀ R,Module K (B R)]
    [∀ R,FiniteDimensional K (B R)]
    (Z : (R : J) → B R →ₗ[K] PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) R.val)
    (hPZ : ∀ R : J,(privateRowMap (K := K) (σ := σ) (n := n) (d := d) (b := b) P R.val).comp (Z R)=0)
    (hwitness : ∀ R : J,∃ p : Space n d q J counts O,
      (privateAugmentedRow hO R p P).ker=((rowConstants hO R p).prodMap (Z R)).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → ∀ R : J,
        (privateAugmentedRow hO R p P).ker=((rowConstants hO R p).prodMap (Z R)).range := by
  classical
  choose p hp using hwitness
  choose D hD hgood using fun R =>
    private_boundary_row_principal_open hO hJ R P (Z R) (hPZ R) (p R) (hp R)
  have hnz (R : J) : D R≠0 := by
    intro hz
    exact hD R (by rw [hz,map_zero])
  obtain ⟨a,ha⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ R,D R,⟨(Module.finBasis K _).equivFun.symm a,?_⟩,?_⟩
  · simp only [LinearEquiv.apply_symm_apply,map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun R _ => ha R)
  intro p hp R
  rw [map_prod] at hp
  exact hgood R p (Finset.prod_ne_zero_iff.mp hp R (Finset.mem_univ R))

end Froberg.PreparedParameters
