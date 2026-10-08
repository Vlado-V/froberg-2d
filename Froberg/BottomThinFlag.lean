import Froberg.BottomVectorSlices
import Froberg.CountedJointSelection

/-! The actual B.3 child-flag certificate supplies bottom-row thin slices
with the dimension of the bottom target itself. -/
noncomputable section
set_option maxHeartbeats 900000
namespace Froberg
open Module MvPolynomial VectorMultiplicationCoordinates BilinearScalarFamily
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}

theorem bottomCoordinateTarget_finrank (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) :
    finrank K (OddTargetRowQuotient
      (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i))
      (oddTargetBottomIndex hd))=
    finrank K (ScalarQuotient (VectorExpansionOpen.quotientMultiplication g d) Q) :=
  ((bottomVectorTargetEquiv hd Q g).trans (bottomCoordinateTargetEquiv hd Q g)).finrank_eq.symm

theorem bottomCoordinateScalarAction_thin_slices (hd : 1 ≤ d)
    (Q : Fin q → Forms K m d) (g : Fin f → Rows K h m (d-1)) (j : ℕ) (C : ℝ)
    (hj : finrank K (ScalarQuotient (VectorExpansionOpen.quotientMultiplication g d) Q)=j)
    (hs : HasClosedKernelSlices
      (scalarQuotientBilinear (VectorExpansionOpen.quotientMultiplication g d) Q)
      (BilinearCovectorStrata.thinSlices j C)) :
    HasClosedKernelSlices (bottomCoordinateScalarAction hd Q g)
      (BilinearCovectorStrata.thinSlices
        (finrank K (OddTargetRowQuotient
          (fun i => scalarEvenBiform (h := h) (Q i))
          (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i))
          (oddTargetBottomIndex hd))) C) := by
  rw [bottomCoordinateTarget_finrank,hj]
  exact bottomCoordinateScalarAction_closed_slices hd Q g _ hs

theorem ChildFlagCondition.bottom_thin_slices (hd : 1 ≤ d)
    (g : Fin f → Rows K h m (d-1)) (j : ℕ) (C : ℝ)
    (a : CoefficientIndex m d q → K)
    (ha : ChildFlagCondition (VectorExpansionOpen.quotientMultiplication g d) j C a) :
    HasClosedKernelSlices (bottomCoordinateScalarAction hd (coefficientForms K m d q a) g)
      (BilinearCovectorStrata.thinSlices
        (finrank K (OddTargetRowQuotient
          (fun i => scalarEvenBiform (h := h) (coefficientForms K m d q a i))
          (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i))
          (oddTargetBottomIndex hd))) C) := by
  rcases ha with ⟨_,_,_,_,hj,hs⟩
  exact bottomCoordinateScalarAction_thin_slices hd _ g j C hj hs

theorem ChildFlagCondition.bottom_thin_slices_coordinates (hd : 1 ≤ d)
    (g : Fin f → Rows K h m (d-1)) (Q : Fin q → Forms K m d) (j : ℕ) (C : ℝ)
    (ha : ChildFlagCondition (VectorExpansionOpen.quotientMultiplication g d) j C
      (coefficientCoordinates Q)) :
    HasClosedKernelSlices (bottomCoordinateScalarAction hd Q g)
      (BilinearCovectorStrata.thinSlices
        (finrank K (OddTargetRowQuotient
          (fun i => scalarEvenBiform (h := h) (Q i))
          (fun i => oddBiformEmbedding hd (by decide) (bottomTensorFamily g i))
          (oddTargetBottomIndex hd))) C) := by
  let ec := coefficientCoordinates (K := K) (n := m) (d := d) (r := q)
  obtain ⟨a,rfl⟩ := ec.symm.surjective Q
  have ha' : ChildFlagCondition (VectorExpansionOpen.quotientMultiplication g d) j C a := by
    change ChildFlagCondition (VectorExpansionOpen.quotientMultiplication g d) j C (ec (ec.symm a)) at ha
    rw [ec.apply_symm_apply] at ha
    exact ha
  exact ChildFlagCondition.bottom_thin_slices hd g j C a ha'

end Froberg
