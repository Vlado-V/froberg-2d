import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! Rank bounds for actual triangular systems of linear equations. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K : Type*} [Field K] {n : ℕ}
variable {V W : Fin n → Type*}
  [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)] [∀ i,FiniteDimensional K (V i)]
  [∀ i,AddCommGroup (W i)] [∀ i,Module K (W i)] [∀ i,FiniteDimensional K (W i)]

/-- The diagonal map in a specified block of an actual linear system. -/
def diagonalBlock (F : ((i : Fin n) → V i) →ₗ[K] ((i : Fin n) → W i)) (i : Fin n) :
    V i →ₗ[K] W i := (LinearMap.proj i).comp (F.comp (LinearMap.single K V i))

/-- Off-diagonal terms do not lower the sum of diagonal ranks in a triangular
system. No independence of those off-diagonal terms is assumed. -/
theorem triangular_rank_lower
    (F : ((i : Fin n) → V i) →ₗ[K] ((i : Fin n) → W i))
    (htri : ∀ i j : Fin n,i<j → ∀ v : V j,F (Pi.single j v) i=0) :
    (∑ i,finrank K (diagonalBlock F i).range) ≤ finrank K F.range := by
  classical
  let f := diagonalBlock F
  have hex (i : Fin n) : ∃ g : (f i).range →ₗ[K] V i,
      (f i).rangeRestrict.comp g=LinearMap.id :=
    (f i).rangeRestrict.exists_rightInverse_of_surjective (f i).range_rangeRestrict
  choose g hg using hex
  have hdiag (i : Fin n) (v : (f i).range) : f i (g i v)=v.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun (hg i) v)
  let G : ((i : Fin n) → (f i).range) →ₗ[K] ((i : Fin n) → V i) := LinearMap.piMap g
  let T := F.comp G
  have hT : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hzero : ∀ i : Fin n,x i=0 := by
      intro i
      induction i using Fin.strong_induction_on with
      | h i ih =>
        apply Subtype.ext
        have hrow := congrFun hx i
        have he : T x i=(x i).val := by
          have heG : G x=∑ j,Pi.single j (g j (x j)) := by
            ext j
            simp [G]
          change F (G x) i=(x i).val
          rw [heG,map_sum,Finset.sum_apply,Finset.sum_eq_single i]
          · exact hdiag i (x i)
          · intro j _ hji
            rcases lt_or_gt_of_ne hji with hj | hj
            · rw [ih j hj,map_zero,Pi.single_zero,map_zero]
              rfl
            · exact htri i j hj _
          · simp
        exact he.symm.trans hrow
    exact funext hzero
  calc
    (∑ i,finrank K (diagonalBlock F i).range) = finrank K ((i : Fin n) → (f i).range) := by
      rw [Module.finrank_pi_fintype]
    _ = finrank K T.range := (LinearMap.finrank_range_of_inj hT).symm
    _ ≤ finrank K F.range := Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

end Froberg
