import Froberg.OddEvenAffineRelations
import Froberg.OddEvenBottomDetection
import Froberg.SurjectiveSplitTarget
import Froberg.OddAmbientProduct

/-! The actual appended odd quotient satisfies the zero-bottom exclusion
used by the common scalar incidence theorem. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}
variable {W₀ H : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup H] [Module K H]

theorem odd_affine_bottom_detects
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (a : Fin e → Forms K m d)
    (ec : (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G) ≃ₗ[K] W₀ × H)
    (hw : ∀ v : biformParitySpace K h m (2*d) 1,
      v.val.IsWeightedHomogeneous (blockWeight h m) 1 →
        (ec ((ambientOddRelations Q F G).mkQ v)).2=0)
    (hupper : Function.Surjective (upperTargetMap
      (backgroundEnumeratedForms (Fin.append Q (oddEvenAffineFamily E a)) F G)))
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) →ₗ[K] K)
    (hA : oddEvenAffineRelations Q F G E a≤ell.ker)
    (hb : quotientSplitBottom ec (oddAmbientToFull Q F G) ell=0) : ell=0 := by
  apply odd_even_append_bottom_detects Q F G (oddEvenAffineFamily E a) hupper ell hA
  intro v hv
  have he := quotientSplit_evaluation ec (oddAmbientToFull Q F G) ell
    ((ambientOddRelations Q F G).mkQ v)
  rw [hw v hv,hb,LinearMap.zero_apply,map_zero,zero_add] at he
  exact he

end Froberg
