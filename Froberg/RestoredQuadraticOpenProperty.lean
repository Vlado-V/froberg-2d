import Froberg.RestoredQuadraticFormalProperty

/-! Actual enlarged restored families satisfy C.2 on a nonempty open.
The scalar threshold precedes every choice of the shared quadratic frame. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module Filter MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

def HasRestoredFormalQuadraticOpen (hdp : 1≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r) : Prop :=
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
    (∃ p : RestoredOuterSpace m d q f J counts O,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : RestoredOuterSpace m d q f J counts O,
      eval ((Module.finBasis K _).equivFun p) D≠0 →
        RestoredFormalQuadraticSeparation hdp he hO hJ heven idx slot p

end Froberg.PreparedParameters
