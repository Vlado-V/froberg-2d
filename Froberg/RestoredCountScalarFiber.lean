import Froberg.PreparedCountScalarFiber
import Froberg.RestoredScalarFiber

/-! The refined scalar fiber for an enlarged restored family fixes the
temporary slots, every high term, the pure tuple, and the outer family. -/
noncomputable section
set_option maxHeartbeats 150000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def restoredCountScalarFiberLinear (hc : ∀ j ∈ J, c j ≤ c' j) :
    PositiveScalars (K := K) m d J c × RestoredOuterSpace m d q f J c' O →ₗ[K]
      RestoredOuterSpace m d q f J c' O where
  toFun x := ((countScalarFiberLinear hc (x.1,x.2.1.1),x.2.1.2),x.2.2)
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · exact (countScalarFiberLinear hc).map_add (x.1,x.2.1.1) (y.1,y.2.1.1)
      · rfl
    · rfl
  map_smul' t x := by
    apply Prod.ext
    · apply Prod.ext
      · exact (countScalarFiberLinear hc).map_smul t (x.1,x.2.1.1)
      · rfl
    · rfl

@[simp] theorem restoredCountScalarFiberLinear_pure (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : RestoredOuterSpace m d q f J c' O) :
    (restoredCountScalarFiberLinear hc (a,p)).1.2=p.1.2 := rfl

@[simp] theorem restoredCountScalarFiberLinear_outer (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : RestoredOuterSpace m d q f J c' O) :
    (restoredCountScalarFiberLinear hc (a,p)).2=p.2 := rfl

theorem restoredCountScalarFiberLinear_extra_generator (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : RestoredOuterSpace m d q f J c' O)
    (j : J) (i : Fin (c' j.val)) (hi : c j.val ≤ i.val) :
    generator (restoredCountScalarFiberLinear hc (a,p)).1.1 (Sum.inr ⟨j,i⟩)=
      generator p.1.1 (Sum.inr ⟨j,i⟩) :=
  countScalarFiberLinear_extra_generator hc a p.1.1 j i hi

theorem restoredCountScalarFiberLinear_restrict (hc : ∀ j ∈ J, c j ≤ c' j)
    (a : PositiveScalars (K := K) m d J c) (p : RestoredOuterSpace m d q f J c' O) :
    restoredRestrictCounts hc (restoredCountScalarFiberLinear hc (a,p))=
      restoredScalarFiberCoordinates.symm
        (a,(restoredScalarFiberCoordinates (restoredRestrictCounts hc p)).2) := by
  apply Prod.ext
  · apply Prod.ext
    · exact countScalarFiberLinear_restrict hc a p.1.1
    · rfl
  · rfl

theorem restoredCountScalarFiberLinear_at (hc : ∀ j ∈ J, c j ≤ c' j)
    (p : RestoredOuterSpace m d q f J c' O) :
    restoredCountScalarFiberLinear hc
      ((restoredScalarFiberCoordinates (restoredRestrictCounts hc p)).1,p)=p := by
  apply Prod.ext
  · apply Prod.ext
    · exact countScalarFiberLinear_at hc p.1.1
    · rfl
  · rfl

theorem principal_open_restored_count_scalar_fiber_at (hc : ∀ j ∈ J, c j ≤ c' j)
    (hO : ∀ j ∈ J, O j ≤ Forms K h j) :
    letI : Module.Finite K (Space m d q J c' O) := finite_space hO
    ∀ (D : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J c' O))) K)
      (p : RestoredOuterSpace m d q f J c' O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      ∃ A : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J c))) K,
        eval ((Module.finBasis K _).equivFun
          (restoredScalarFiberCoordinates (restoredRestrictCounts hc p)).1) A ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) A ≠ 0 →
          eval ((Module.finBasis K _).equivFun (restoredCountScalarFiberLinear hc (a,p))) D ≠ 0 := by
  letI : Module.Finite K (Space m d q J c' O) := finite_space hO
  intro D p hp
  apply principal_open_freeze_at (restoredCountScalarFiberLinear hc)
    (restoredScalarFiberCoordinates (restoredRestrictCounts hc p)).1 p D
  simpa only [restoredCountScalarFiberLinear_at] using hp

end Froberg.PreparedParameters
