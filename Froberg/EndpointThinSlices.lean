import Froberg.OddEndpointScalarSlices
import Froberg.OddRelativeDimensions

/-! The scalar slice index is the dimension of the actual enlarged odd
endpoint target, using the proved relative injection. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem oddEndpointScalarAction_target_finrank
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (hi : Function.Injective (oddEvenRelativeMap Q F G E)) :
    finrank K (oddTargetSpace ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms (Fin.append Q E) F G))=
      finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G)-
        e*finrank K (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) := by
  rw [←(oddEvenEndpointExtensionEquiv Q F G E).finrank_eq]
  exact Nat.eq_sub_of_add_eq (injective_pi_quotient_finrank (oddEvenRelativeMap Q F G E) hi).symm

theorem oddEndpointScalarAction_closed_thin_slices
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (hi : Function.Injective (oddEvenRelativeMap Q F G E)) (C : ℝ)
    (hs : HasClosedKernelSlices
      (targetPostcompose (oddBackgroundScalarProduct Q F G) (oddEvenRelativeMap Q F G E).range.mkQ)
      (BilinearCovectorStrata.thinSlices
        (finrank K (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G)-
          e*finrank K (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G)) C)) :
    HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q E) F G)
      (BilinearCovectorStrata.thinSlices
        (finrank K (oddTargetSpace ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
          (backgroundEnumeratedForms (Fin.append Q E) F G))) C) := by
  rw [oddEndpointScalarAction_target_finrank Q F G E hi]
  exact oddEndpointScalarAction_closed_slices Q F G E _ hs

end Froberg
