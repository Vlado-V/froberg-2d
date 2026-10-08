import Quartic.SmallCovectorMotion
import Quartic.AuxiliaryMotionMatrix
import Quartic.ActualTraceMotion
import Quartic.ActualCorrectionMotion

/-! The actual two motion matrices exclude all small-range ambient covectors. -/
noncomputable section
namespace Quartic.ActualSmallMotionAvoidance
open Module MvPolynomial Matrix KernelPolynomialCharts UniformEndpoint ProfileCertificate
open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts SmallCovectorCommonOpen
open PolynomialBilinearCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K] {m : ℕ} {upper : Bool}
set_option maxHeartbeats 1500000

abbrev Parameters := SmallCovectorMotion.Parameters
abbrev G (p : Parameters K m upper) := AugmentedGeneric.coefficientMixed (baseProjection p)
abbrev Q (p : Parameters K m upper) := AugmentedGeneric.coefficientChild (baseProjection p)
abbrev Marked (p : Parameters K m upper) := Submodule K (ActualCorrectionMotion.ChildQuotient (Q p))

def correctionCount (p : Parameters K m upper) (U : Marked p) : ℕ :=
  (Counts.H m (upperEndpoint m) (mixedCount m upper)+3+finrank K U).toNat

def auxiliaryCount (p : Parameters K m upper) (U : Marked p) : ℕ :=
  (Counts.j m (upperEndpoint m) (mixedCount m upper)-
    ((2*m+2*mixedCount m upper : ℕ):ℤ)-correctionCount p U).toNat

/-- Actual augmented-injective pure motions, actual mixed motions, and the
minimal number of auxiliary target vectors exclude every common covector.
All relation-kernel strata are handled, with no remaining motion-rank premise. -/
theorem exists_matrix_motions (hm : 28 ≤ m) (p : Parameters K m upper)
    (hp : ClosedConditions p) (U : Marked p)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (hs : Function.Surjective (ActualCorrectionMotion.middleMap (G p) (Q p)))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed (G p))))
    (r₀ : ActualCorrectionMotion.Pure K m)
    (hr₀ : Function.Injective (AugmentedGeneric.quotientAugmented
      (AugmentedGeneric.productMap (G p)) (Q p) r₀)) :
    ∃ sectionMap : ActualCorrectionMotion.MiddleTarget (Q p) →ₗ[K]
        ActualCorrectionMotion.Raw K m (mixedCount m upper),
      (ActualCorrectionMotion.middleMap (G p) (Q p)).comp sectionMap=LinearMap.id ∧
      ∃ x : ActualCorrectionMotion.PureIndex m → K,
        ∃ y : AuxiliaryMotionMatrix.Input K
          (Fintype.card (Fin (mixedCount m upper) × Fin (FormCount m 2))) (RowCount m 3)
          (auxiliaryCount p U),
        Function.Injective (AugmentedGeneric.quotientAugmented
          (AugmentedGeneric.productMap (G p)) (Q p) (ActualCorrectionMotion.pureCoordinates.symm x)) ∧
        ∀ ell : Fin (RowCount m 3) → K,
          (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (SmallCovectorMotion.mixed p j))=0) →
          (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (SmallCovectorMotion.child p i) v)=0) →
          evaluated (ActualTraceMotion.covectorMatrix (G p)) ell *ᵥ x=0 →
          evaluated (ActualCorrectionMotion.finitePolynomialConstraint (G p) (Q p) U sectionMap)
            (Sum.elim ell x) *ᵥ y.1=0 →
          (∀ j,covector ell (y.2 j)=0) → ell=0 := by
  classical
  obtain ⟨sectionMap,hsection⟩ := ActualCorrectionMotion.exists_section (G p) (Q p) hs
  let A := ActualTraceMotion.covectorMatrix (G p)
  let B := ActualCorrectionMotion.finitePolynomialConstraint (G p) (Q p) U sectionMap
  let B' := AuxiliaryMotionMatrix.polynomialMatrix (e := auxiliaryCount p U) B
    (fun k => X (Sum.inl k))
  let Good := fun z : Fin (Fintype.card (Fin 4 × Fin (FormCount m 2))) ⊕
      Fin (finrank K (AuxiliaryMotionMatrix.Input K
        (Fintype.card (Fin (mixedCount m upper) × Fin (FormCount m 2)))
        (RowCount m 3) (auxiliaryCount p U))) → K =>
    Function.Injective (AugmentedGeneric.quotientAugmented (AugmentedGeneric.productMap (G p))
      (Q p) (ActualCorrectionMotion.pureCoordinates.symm (fun i => z (Sum.inl i))))
  have hdim : (correctionCount p U : ℤ)=Counts.H m (upperEndpoint m) (mixedCount m upper)+3+finrank K U := by
    have hd := MovingMiddleCorrection.coefficientImage_finrank (G p) (Q p) r₀ hg hh hr₀ hs U
    apply Int.toNat_of_nonneg
    rw [← hd]
    exact Int.natCast_nonneg _
  have hA : ∀ (s : K) ell,evaluated A (s • ell)=s • evaluated A ell := by
    intro s ell
    exact ActualTraceMotion.eval_covectorMatrix_smul (G p) ell s
  have hB : ∀ (s : K) ell x,evaluated B' (Sum.elim (s • ell) x)=s • evaluated B' (Sum.elim ell x) := by
    intro s ell x
    apply AuxiliaryMotionMatrix.polynomialMatrix_scaling B
    intro s ell x
    exact ActualCorrectionMotion.finitePolynomialConstraint_scaling (G p) (Q p) U sectionMap s ell x
  have hcount (d : Threshold m upper) : ConvolutionClosedSlices.sliceCount m upper d.val ≤
      (2*m+2*mixedCount m upper-4*d.val)+
        ((correctionCount p U-mixedCount m upper*d.val)+auxiliaryCount p U) := by
    have h := SmallCovectorMotion.slice_budget (Counts.j m (upperEndpoint m) (mixedCount m upper))
      (2*m+2*mixedCount m upper) (correctionCount p U) (mixedCount m upper) d.val
    simpa only [ConvolutionClosedSlices.sliceCount,auxiliaryCount,sub_add_eq_sub_sub,
      Nat.add_assoc] using h
  have hr1 : ∀ d : Threshold m upper,∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
      (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (SmallCovectorMotion.mixed p j))=0) →
      (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (SmallCovectorMotion.child p i) v)=0) →
      finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate ell))=
        d.val+mixedCount m upper → ∀ z,Good z →
      2*m+2*mixedCount m upper-4*d.val ≤ (evaluated A ell).rank := by
    intro d ell _ hE _ hker _ _
    apply ActualTraceMotion.eval_covectorMatrix_rank_bound_of_ambient (G p) hg htrace ell
    · intro j f
      have hj := hE j (finiteEquiv f)
      simpa only [SmallCovectorMotion.mixed,RowMultiplicationCoordinates.coordinate_apply,
        LinearEquiv.symm_apply_apply] using hj
    · exact hker.le
  have hr2 : ∀ d : Threshold m upper,∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
      (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (SmallCovectorMotion.mixed p j))=0) →
      (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (SmallCovectorMotion.child p i) v)=0) →
      finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate ell))=
        d.val+mixedCount m upper → ∀ z,Good z →
      evaluated A ell *ᵥ (fun i => z (Sum.inl i))=0 →
      (correctionCount p U-mixedCount m upper*d.val)+auxiliaryCount p U ≤
        (evaluated B' (Sum.elim ell (fun i => z (Sum.inl i)))).rank := by
    intro d ell hell hE _ hker z hGood _
    have hE' : Submodule.span K (Set.range (G p)) ≤ LinearMap.ker (ActualCorrectionMotion.sourceRelation ell) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change relationMap RowMultiplicationCoordinates.coordinate ell (rowFiniteEquiv (G p j))=0
      exact (AmbientCovectorTransport.mem_relationMap_ker_iff _ _ _).mpr (hE j)
    have hraw := ActualCorrectionMotion.constraint_rank_bound_ambient (G p) (Q p) U sectionMap hsection
      (ActualCorrectionMotion.pureCoordinates.symm (fun i => z (Sum.inl i))) ell d.val hE'
      (by omega) hg hh hGood hs
    have hfinite := ActualCorrectionMotion.finitePolynomialConstraint_rank (G p) (Q p) U sectionMap
      ell (fun i => z (Sum.inl i))
    have hbase : correctionCount p U-mixedCount m upper*d.val ≤
        (evaluated B (Sum.elim ell (fun i => z (Sum.inl i)))).rank := by
      change correctionCount p U-mixedCount m upper*d.val ≤
        ((ActualCorrectionMotion.finitePolynomialConstraint (G p) (Q p) U sectionMap).map
          (eval (Sum.elim ell (fun i => z (Sum.inl i))))).rank
      rw [hfinite]
      omega
    have haux := AuxiliaryMotionMatrix.polynomialMatrix_rank (e := auxiliaryCount p U) B
      (fun k => X (Sum.inl k)) (Sum.elim ell (fun i => z (Sum.inl i))) (by simpa using hell)
    change _ ≤ (evaluated (AuxiliaryMotionMatrix.polynomialMatrix B (fun k => X (Sum.inl k))) _).rank
    rw [haux]
    omega
  obtain ⟨P,⟨z₀,hz₀⟩,havoid⟩ := SmallCovectorMotion.principal_open_all_kernel_ranks hm p hp hg
    A B' hA hB (fun d => 2*m+2*mixedCount m upper-4*d.val)
    (fun d => correctionCount p U-mixedCount m upper*d.val+auxiliaryCount p U)
    hcount Good hr1 hr2
  obtain ⟨D,hD,hGood⟩ := SmallCovectorMotion.augmented_motion_open (G p) (Q p)
    ActualCorrectionMotion.pureCoordinates r₀ hh hr₀
  have hPnz : P ≠ 0 := by intro h; simp [h] at hz₀
  let D' : MvPolynomial (ActualCorrectionMotion.PureIndex m ⊕ Fin (finrank K
      (AuxiliaryMotionMatrix.Input K
        (Fintype.card (Fin (mixedCount m upper) × Fin (FormCount m 2)))
        (RowCount m 3) (auxiliaryCount p U)))) K := rename Sum.inl D
  have hDn : D' ≠ 0 := by
    intro h
    have hv : eval (Sum.elim (ActualCorrectionMotion.pureCoordinates r₀)
      (0 : Fin (finrank K (AuxiliaryMotionMatrix.Input K
        (Fintype.card (Fin (mixedCount m upper) × Fin (FormCount m 2)))
        (RowCount m 3) (auxiliaryCount p U))) → K)) D' ≠ 0 := by
      simpa [D',eval_rename,Function.comp_def] using hD
    simp only [h,map_zero,ne_eq,not_true_eq_false] at hv
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hPnz hDn)
  rw [map_mul,mul_ne_zero_iff] at hz
  have hzGood : Good z := hGood _ (by simpa [D',eval_rename,Function.comp_def] using hz.2)
  let x := fun i => z (Sum.inl i)
  let y := (coordinates K (AuxiliaryMotionMatrix.Input K
    (Fintype.card (Fin (mixedCount m upper) × Fin (FormCount m 2)))
    (RowCount m 3) (auxiliaryCount p U))).symm (fun j => z (Sum.inr j))
  refine ⟨sectionMap,hsection,x,y,hzGood,?_⟩
  intro ell hE hQ hfirst hsecond hZ
  by_contra hell
  have h := havoid z hz.1 hzGood ell hell hE hQ
  have hb : evaluated B' (Sum.elim ell x) *ᵥ (fun j => z (Sum.inr j))=0 := by
    have hy := (AuxiliaryMotionMatrix.polynomialMatrix_kernel_iff B (fun k => X (Sum.inl k))
      (Sum.elim ell x) y).mpr ⟨hsecond,by simpa only [eval_X,Sum.elim_inl] using hZ⟩
    simpa only [y,LinearEquiv.apply_symm_apply] using hy
  exact h.elim (fun h => h hfirst) (fun h => h hb)

/-- The same exclusion stated solely with actual polynomial products and
actual ambient covectors. This is the input to the response-rank theorem. -/
theorem exists_actual_motions (hm : 28 ≤ m) (p : Parameters K m upper)
    (hp : ClosedConditions p) (U : Marked p)
    (hg : LinearIndependent K (G p)) (hh : LinearIndependent K (Q p))
    (hs : Function.Surjective (ActualCorrectionMotion.middleMap (G p) (Q p)))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed (G p))))
    (r₀ : ActualCorrectionMotion.Pure K m)
    (hr₀ : Function.Injective (AugmentedGeneric.quotientAugmented
      (AugmentedGeneric.productMap (G p)) (Q p) r₀)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin (mixedCount m upper) → Forms K m 2,
      ∃ Z : Fin (auxiliaryCount p U) → Rows K m 3,
        Function.Injective (AugmentedGeneric.quotientAugmented
          (AugmentedGeneric.productMap (G p)) (Q p) r) ∧
        ∀ ell : Rows K m 3 →ₗ[K] K,
          (∀ j f,ell (multiplication f (G p j))=0) →
          (∀ i v,ell (multiplication (Q p i) v)=0) →
          (∀ z : ActualTraceMotion.CycleParameters K m (mixedCount m upper),
            ell (∑ i : Fin 4,multiplication (r i) (ActualTraceMotion.rawRows (G p) z i))=0) →
          (∀ a : (MovingMiddleCorrection.traceSpace (Q p) r U).comap
            (ActualCorrectionMotion.middleMap (G p) (Q p)),
            ell (∑ i : Fin (mixedCount m upper),multiplication (s i) (a.val i))=0) →
          (∀ j,ell (Z j)=0) → ell=0 := by
  classical
  obtain ⟨sectionMap,hsection,x,y,haug,havoid⟩ :=
    exists_matrix_motions hm p hp U hg hh hs htrace r₀ hr₀
  let r := ActualCorrectionMotion.pureCoordinates.symm x
  let s := ActualCorrectionMotion.motionDecode y.1
  have hr : ActualTraceMotion.motionDecode x=r := rfl
  refine ⟨r,s,fun j => rowFiniteEquiv.symm (y.2 j),haug,?_⟩
  intro ell hE hQ hfirst hsecond hZ
  let lam := AmbientCovectorTransport.dualCoordinates rowFiniteEquiv ell
  apply (AmbientCovectorTransport.dualCoordinates_eq_zero_iff rowFiniteEquiv ell).mp
  apply havoid lam
  · intro j f
    rw [RowMultiplicationCoordinates.coordinate_apply,AmbientCovectorTransport.covector_dualCoordinates,
      LinearEquiv.symm_apply_apply]
    simpa only [SmallCovectorMotion.mixed,LinearEquiv.symm_apply_apply] using hE j (finiteEquiv.symm f)
  · intro i v
    rw [RowMultiplicationCoordinates.coordinate_apply,AmbientCovectorTransport.covector_dualCoordinates,
      LinearEquiv.symm_apply_apply]
    simpa only [SmallCovectorMotion.child,LinearEquiv.symm_apply_apply] using hQ i (rowFiniteEquiv.symm v)
  · apply (ActualTraceMotion.eval_covectorMatrix_kernel_iff (G p) lam x).mpr
    intro z
    simpa only [hr,lam,AmbientCovectorTransport.covector_dualCoordinates,LinearEquiv.symm_apply_apply]
      using hfirst z
  · change (ActualCorrectionMotion.finitePolynomialConstraint (G p) (Q p) U sectionMap).map
      (eval (Sum.elim lam x)) *ᵥ y.1=0
    rw [ActualCorrectionMotion.finitePolynomialConstraint_mulVec]
    change ActualCorrectionMotion.constraint (G p) (Q p) U sectionMap r lam *ᵥ
      ActualCorrectionMotion.motionEncode s=0
    apply (ActualCorrectionMotion.constraint_kernel_iff (G p) (Q p) U sectionMap
      hsection r lam (ActualCorrectionMotion.motionEncode s)).mpr
    intro a ha
    simpa only [ActualCorrectionMotion.motionEncode,LinearMap.coe_mk,AddHom.coe_mk,
      LinearEquiv.symm_apply_apply,lam,AmbientCovectorTransport.covector_dualCoordinates]
      using hsecond ⟨a,ha⟩
  · intro j
    rw [AmbientCovectorTransport.covector_dualCoordinates]
    exact hZ j

end Quartic.ActualSmallMotionAvoidance
