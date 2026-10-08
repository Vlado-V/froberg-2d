import Froberg.GradedNormalized
import Froberg.NormalizedCutoff
import Froberg.PureCutoff

/-! The pure family U and the quotient projection in C.3 can be chosen
simultaneously, with both the next-degree cutoff and the uniform normalized
linear multiplication estimate. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic
variable {K : Type*} [Field K] [Infinite K] {n e u b : ℕ}

theorem exists_projected_linear_growth_with_cutoff (hn : 0<n) (he : 0<e)
    (hW : (n+(1+e)-1).choose (1+e)=u+b)
    (hmargin : ((n+e-1).choose e)*((n+e-1).choose e)<u*b)
    (hlarge : (e+2)*(e+2)*(e+1)≤n)
    (hcut : (n+(e+2)-1).choose (e+2)≤u*n) :
    ∃ P : Forms K n (1+e) →ₗ[K] (Fin b → K),
      Function.Surjective P ∧ finrank K P.ker=u ∧
      (∀ L : Submodule K (Forms K n e),
        b*finrank K L≤finrank K (Forms K n e)*
          finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P)) ∧
      BilinearImage.image (gradedMultiplication (K := K) (n := n) (d := 1+e) (e := 1)).flip P.ker=⊤ := by
  obtain ⟨U,hU,hfill⟩ := exists_pure_cutoff_subspace (K := K) (d := 1+e) (r := u)
    hn (by omega) (by simpa [Nat.choose_one_right,Nat.mul_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hlarge)
    (by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hcut) (by omega)
  apply exists_normalized_projection_with_cutoff
    (show 0<finrank K (Forms K n e) by
      rw [finrank_forms K n e hn]
      exact Nat.choose_pos (by omega))
    (by simpa only [finrank_forms K n (1+e) hn] using hW)
    (by simpa only [finrank_forms K n e hn] using hmargin)
    (gradedMultiplication (d := 1) (e := e))
    (graded_normalized_growth hn)
    (gradedMultiplication (K := K) (n := n) (d := 1+e) (e := 1)).flip U hU hfill

end Froberg
