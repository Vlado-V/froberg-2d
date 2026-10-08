import Froberg.PreparedFiniteRows
import Froberg.PreparedQuadraticRow

/-! Finite arithmetic capacities and the proved scalar opens produce all
positive even coefficient rows on one actual prepared-family open. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

instance constrainedSpaceFinite {w n d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) :
    Module.Finite K (Space n d q J counts (constrainedOutputs T)) :=
  finite_space (fun _ _ => inf_le_left)

/-- The finite B.4 row constructor in a single coefficient space. -/
theorem rows_open_of_capacities {w v d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hJ : ∀ j∈J,2≤j) (hdegree : ∀ j∈J,j≤d) (h2 : 2∈J)
    (hquad : ∃ b,QuadraticRowCapacity (v+v) d q b J counts (constrainedOutputs T))
    (hhigher : ∀ R : J,R.val≠2 → ∃ b,HigherRowCapacity w v d q b J counts T R) :
    let S := Space (v+v) d q J counts (constrainedOutputs T)
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
      ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
        ∀ R : J,(row (fun _ _ => inf_le_left) R p).ker=
          (rowConstants (fun _ _ => inf_le_left) R p).range := by
  letI : Module.Finite K (Space (v+v) d q J counts (constrainedOutputs T)) :=
    finite_space (fun _ _ => inf_le_left)
  apply rows_common_open (O := constrainedOutputs T) (fun _ _ => inf_le_left) hdegree
  intro R
  by_cases hR : R.val=2
  · have hReq : R=(⟨2,h2⟩ : J) := Subtype.ext hR
    subst R
    obtain ⟨b,hb⟩ := hquad
    exact exists_quadratic_row_parameter (fun _ _ => inf_le_left) hJ h2 hb
  · obtain ⟨b,hb⟩ := hhigher R hR
    exact exists_higher_row_parameter R hb

end Froberg.PreparedParameters
