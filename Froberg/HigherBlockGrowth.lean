module

public import Froberg.BlockBilinearGrowth

@[expose] public section

/-! The common higher-layer rate only charges kernel directions outside
the bottom initial piece. This includes arbitrary graph subspaces. -/
noncomputable section
namespace Froberg
open Module Quartic.FilteredImage
variable {K P : Type*} [Field K] [AddCommGroup P] [Module K P]
variable {n : ℕ} {V W : Fin (n+1) → Type*}
  [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)] [∀ i,FiniteDimensional K (V i)]
  [∀ i,AddCommGroup (W i)] [∀ i,Module K (W i)] [∀ i,FiniteDimensional K (W i)]

theorem blockBilinear_higher_growth
    (mu : (i : Fin (n+1)) → P →ₗ[K] V i →ₗ[K] W i) (rate : ℕ)
    (hmu : ∀ i : Fin n,∀ S : Submodule K (V i.succ),rate*finrank K S≤
      finrank K (Quartic.BilinearImage.image (mu i.succ) S))
    (L : Submodule K ((i : Fin (n+1)) → V i)) :
    rate*(finrank K L-finrank K (initialPiece V L 0))≤
      finrank K (Quartic.BilinearImage.image (blockBilinear mu) L) := by
  let rates : Fin (n+1) → ℕ := Fin.cases 0 (fun _ => rate)
  have hrates : ∀ i (S : Submodule K (V i)),rates i*finrank K S≤
      finrank K (Quartic.BilinearImage.image (mu i) S) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro S
      simp only [rates,Fin.cases_zero,zero_mul]
      exact Nat.zero_le _
    · exact hmu j
  have hg := blockBilinear_weighted_growth mu rates hrates L
  have hd := sum_initialPiece_finrank V L
  rw [Fin.sum_univ_succ] at hd
  have hdim : (∑ i : Fin n,finrank K (initialPiece V L i.succ))=
      finrank K L-finrank K (initialPiece V L 0) := by omega
  rw [Fin.sum_univ_succ] at hg
  simp only [rates,Fin.cases_zero,Fin.cases_succ,zero_mul,zero_add,←Finset.mul_sum] at hg
  rwa [hdim] at hg

end Froberg
