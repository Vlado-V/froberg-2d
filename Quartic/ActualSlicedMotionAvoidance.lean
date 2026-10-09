module

public import Quartic.SmallCovectorMotion
public import Quartic.AmbientSliceMotion
public import Quartic.AuxiliaryMotionMatrix
public import Quartic.ActualTraceMotion
public import Quartic.ActualCorrectionMotion

@[expose] public section

/-! The actual two motion matrices exclude ambient covectors from supplied closed slices. -/
noncomputable section
namespace Quartic.ActualSlicedMotionAvoidance
open Module MvPolynomial Matrix KernelPolynomialCharts UniformEndpoint ProfileCertificate
open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts SmallCovectorCommonOpen
open PolynomialBilinearCoordinates
variable {K : Type*} [Field K] [IsAlgClosed K] {m c q : ℕ}
set_option maxHeartbeats 1500000

abbrev Mixed (K : Type*) [Field K] (m c : ℕ) := Fin c → MiddleCoordinates.Mixed K m
abbrev Child (K : Type*) [Field K] (m q : ℕ) := Fin q → Forms K m 2
abbrev Marked (h : Child K m q) := Submodule K (ActualCorrectionMotion.ChildQuotient h)

def correctionCount (h : Child K m q) (U : Marked h) : ℕ :=
  (Counts.H m q c+3+finrank K U).toNat

def auxiliaryCount (h : Child K m q) (U : Marked h) : ℕ :=
  (Counts.j m q c-((2*m+2*c : ℕ):ℤ)-correctionCount (c := c) h U).toNat

def sliceCount (h : Child K m q) (U : Marked h) (d : ℕ) : ℕ :=
  (2*m+2*c-4*d)+(correctionCount (c := c) h U-c*d)+auxiliaryCount (c := c) h U

def ClosedSlices (g : Mixed K m c) (h : Child K m q) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3) : Prop :=
  ∀ d : AmbientSliceMotion.Threshold (RowCount m 1) c,∀ ell : Fin (RowCount m 3) → K,
    d.val+c ≤ finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate ell)) →
    (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
    (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (finiteEquiv (h i)) v)=0) →
    (∀ j,covector ell (rowFiniteEquiv (Z d j))=0) → ell=0

/-- Actual augmented-injective pure motions, actual mixed motions, and the
minimal number of auxiliary target vectors exclude every common covector.
All relation-kernel strata are handled, with no remaining motion-rank premise. -/
theorem exists_matrix_motions (g : Mixed K m c) (h : Child K m q) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3)
    (hclosed : ClosedSlices g h U Z)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (ActualCorrectionMotion.middleMap g h))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)))
    (r₀ : ActualCorrectionMotion.Pure K m)
    (hr₀ : Function.Injective (AugmentedGeneric.quotientAugmented
      (AugmentedGeneric.productMap g) h r₀)) :
    ∃ sectionMap : ActualCorrectionMotion.MiddleTarget h →ₗ[K]
        ActualCorrectionMotion.Raw K m c,
      (ActualCorrectionMotion.middleMap g h).comp sectionMap=LinearMap.id ∧
      ∃ x : ActualCorrectionMotion.PureIndex m → K,
        ∃ y : AuxiliaryMotionMatrix.Input K
          (Fintype.card (Fin c × Fin (FormCount m 2))) (RowCount m 3)
          (auxiliaryCount (c := c) h U),
        Function.Injective (AugmentedGeneric.quotientAugmented
          (AugmentedGeneric.productMap g) h (ActualCorrectionMotion.pureCoordinates.symm x)) ∧
        ∀ ell : Fin (RowCount m 3) → K,
          (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
          (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (finiteEquiv (h i)) v)=0) →
          evaluated (ActualTraceMotion.covectorMatrix g) ell *ᵥ x=0 →
          evaluated (ActualCorrectionMotion.finitePolynomialConstraint g h U sectionMap)
            (Sum.elim ell x) *ᵥ y.1=0 →
          (∀ j,covector ell (y.2 j)=0) → ell=0 := by
  classical
  obtain ⟨sectionMap,hsection⟩ := ActualCorrectionMotion.exists_section g h hs
  let A := ActualTraceMotion.covectorMatrix g
  let B := ActualCorrectionMotion.finitePolynomialConstraint g h U sectionMap
  let B' := AuxiliaryMotionMatrix.polynomialMatrix (e := auxiliaryCount (c := c) h U) B
    (fun k => X (Sum.inl k))
  let Good := fun z : Fin (Fintype.card (Fin 4 × Fin (FormCount m 2))) ⊕
      Fin (finrank K (AuxiliaryMotionMatrix.Input K
        (Fintype.card (Fin c × Fin (FormCount m 2)))
        (RowCount m 3) (auxiliaryCount (c := c) h U))) → K =>
    Function.Injective (AugmentedGeneric.quotientAugmented (AugmentedGeneric.productMap g)
      h (ActualCorrectionMotion.pureCoordinates.symm (fun i => z (Sum.inl i))))
  have hdim : (correctionCount (c := c) h U : ℤ)=Counts.H m q c+3+finrank K U := by
    have hd := MovingMiddleCorrection.coefficientImage_finrank g h r₀ hg hh hr₀ hs U
    apply Int.toNat_of_nonneg
    rw [← hd]
    exact Int.natCast_nonneg _
  have hA : ∀ (s : K) ell,evaluated A (s • ell)=s • evaluated A ell := by
    intro s ell
    exact ActualTraceMotion.eval_covectorMatrix_smul g ell s
  have hB : ∀ (s : K) ell x,evaluated B' (Sum.elim (s • ell) x)=s • evaluated B' (Sum.elim ell x) := by
    intro s ell x
    apply AuxiliaryMotionMatrix.polynomialMatrix_scaling B
    intro s ell x
    exact ActualCorrectionMotion.finitePolynomialConstraint_scaling g h U sectionMap s ell x
  have hcount (d : AmbientSliceMotion.Threshold (RowCount m 1) c) :
      sliceCount (c := c) h U d.val ≤ (2*m+2*c-4*d.val)+
        ((correctionCount (c := c) h U-c*d.val)+auxiliaryCount (c := c) h U) := by
    dsimp only [sliceCount]
    omega
  have hr1 : ∀ d : AmbientSliceMotion.Threshold (RowCount m 1) c,∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
      (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
      (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (finiteEquiv (h i)) v)=0) →
      finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate ell))=
        d.val+c → ∀ z,Good z →
      2*m+2*c-4*d.val ≤ (evaluated A ell).rank := by
    intro d ell _ hE _ hker _ _
    apply ActualTraceMotion.eval_covectorMatrix_rank_bound_of_ambient g hg htrace ell
    · intro j f
      have hj := hE j (finiteEquiv f)
      simpa only [RowMultiplicationCoordinates.coordinate_apply,
        LinearEquiv.symm_apply_apply] using hj
    · exact hker.le
  have hr2 : ∀ d : AmbientSliceMotion.Threshold (RowCount m 1) c,∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
      (∀ j f,covector ell (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
      (∀ i v,covector ell (RowMultiplicationCoordinates.coordinate (finiteEquiv (h i)) v)=0) →
      finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate ell))=
        d.val+c → ∀ z,Good z →
      evaluated A ell *ᵥ (fun i => z (Sum.inl i))=0 →
      (correctionCount (c := c) h U-c*d.val)+auxiliaryCount (c := c) h U ≤
        (evaluated B' (Sum.elim ell (fun i => z (Sum.inl i)))).rank := by
    intro d ell hell hE _ hker z hGood _
    have hE' : Submodule.span K (Set.range g) ≤ LinearMap.ker (ActualCorrectionMotion.sourceRelation ell) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change relationMap RowMultiplicationCoordinates.coordinate ell (rowFiniteEquiv (g j))=0
      exact (AmbientCovectorTransport.mem_relationMap_ker_iff _ _ _).mpr (hE j)
    have hraw := ActualCorrectionMotion.constraint_rank_bound_ambient g h U sectionMap hsection
      (ActualCorrectionMotion.pureCoordinates.symm (fun i => z (Sum.inl i))) ell d.val hE'
      (by omega) hg hh hGood hs
    have hfinite := ActualCorrectionMotion.finitePolynomialConstraint_rank g h U sectionMap
      ell (fun i => z (Sum.inl i))
    have hbase : correctionCount (c := c) h U-c*d.val ≤
        (evaluated B (Sum.elim ell (fun i => z (Sum.inl i)))).rank := by
      change correctionCount (c := c) h U-c*d.val ≤
        ((ActualCorrectionMotion.finitePolynomialConstraint g h U sectionMap).map
          (eval (Sum.elim ell (fun i => z (Sum.inl i))))).rank
      rw [hfinite]
      omega
    have haux := AuxiliaryMotionMatrix.polynomialMatrix_rank (e := auxiliaryCount (c := c) h U) B
      (fun k => X (Sum.inl k)) (Sum.elim ell (fun i => z (Sum.inl i))) (by simpa using hell)
    change _ ≤ (evaluated (AuxiliaryMotionMatrix.polynomialMatrix B (fun k => X (Sum.inl k))) _).rank
    rw [haux]
    omega
  have hgcoord : LinearIndependent K (fun j => rowFiniteEquiv (g j)) :=
    hg.map' rowFiniteEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr rowFiniteEquiv.injective)
  obtain ⟨P,⟨z₀,hz₀⟩,havoid⟩ := AmbientSliceMotion.principal_open_all_kernel_ranks
    RowMultiplicationCoordinates.coordinate (fun j => rowFiniteEquiv (g j)) (fun i => finiteEquiv (h i))
    hgcoord (fun d => sliceCount (c := c) h U d.val) (fun d j => rowFiniteEquiv (Z d j))
    hclosed A B' hA hB (fun d => 2*m+2*c-4*d.val)
    (fun d => correctionCount (c := c) h U-c*d.val+auxiliaryCount (c := c) h U)
    hcount Good hr1 hr2
  obtain ⟨D,hD,hGood⟩ := SmallCovectorMotion.augmented_motion_open g h
    ActualCorrectionMotion.pureCoordinates r₀ hh hr₀
  have hPnz : P ≠ 0 := by intro h; simp [h] at hz₀
  let D' : MvPolynomial (ActualCorrectionMotion.PureIndex m ⊕ Fin (finrank K
      (AuxiliaryMotionMatrix.Input K
        (Fintype.card (Fin c × Fin (FormCount m 2)))
        (RowCount m 3) (auxiliaryCount (c := c) h U)))) K := rename Sum.inl D
  have hDn : D' ≠ 0 := by
    intro hzero
    have hv : eval (Sum.elim (ActualCorrectionMotion.pureCoordinates r₀)
      (0 : Fin (finrank K (AuxiliaryMotionMatrix.Input K
        (Fintype.card (Fin c × Fin (FormCount m 2)))
        (RowCount m 3) (auxiliaryCount (c := c) h U))) → K)) D' ≠ 0 := by
      simpa [D',eval_rename,Function.comp_def] using hD
    simp only [hzero,map_zero,ne_eq,not_true_eq_false] at hv
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hPnz hDn)
  rw [map_mul,mul_ne_zero_iff] at hz
  have hzGood : Good z := hGood _ (by simpa [D',eval_rename,Function.comp_def] using hz.2)
  let x := fun i => z (Sum.inl i)
  let y := (coordinates K (AuxiliaryMotionMatrix.Input K
    (Fintype.card (Fin c × Fin (FormCount m 2)))
    (RowCount m 3) (auxiliaryCount (c := c) h U))).symm (fun j => z (Sum.inr j))
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
theorem exists_actual_motions (g : Mixed K m c) (h : Child K m q) (U : Marked h)
    (Z : (d : AmbientSliceMotion.Threshold (RowCount m 1) c) →
      Fin (sliceCount (c := c) h U d.val) → Rows K m 3)
    (hclosed : ClosedSlices g h U Z)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (ActualCorrectionMotion.middleMap g h))
    (htrace : Function.Injective (SplitMiddle31.mixedMultiplication (ActualTraceMotion.rowMixed g)))
    (r₀ : ActualCorrectionMotion.Pure K m)
    (hr₀ : Function.Injective (AugmentedGeneric.quotientAugmented
      (AugmentedGeneric.productMap g) h r₀)) :
    ∃ r : Fin 4 → Forms K m 2,∃ s : Fin c → Forms K m 2,
      ∃ Z : Fin (auxiliaryCount (c := c) h U) → Rows K m 3,
        Function.Injective (AugmentedGeneric.quotientAugmented
          (AugmentedGeneric.productMap g) h r) ∧
        ∀ ell : Rows K m 3 →ₗ[K] K,
          (∀ j f,ell (multiplication f (g j))=0) →
          (∀ i v,ell (multiplication (h i) v)=0) →
          (∀ z : ActualTraceMotion.CycleParameters K m c,
            ell (∑ i : Fin 4,multiplication (r i) (ActualTraceMotion.rawRows g z i))=0) →
          (∀ a : (MovingMiddleCorrection.traceSpace h r U).comap
            (ActualCorrectionMotion.middleMap g h),
            ell (∑ i : Fin c,multiplication (s i) (a.val i))=0) →
          (∀ j,ell (Z j)=0) → ell=0 := by
  classical
  obtain ⟨sectionMap,hsection,x,y,haug,havoid⟩ :=
    exists_matrix_motions g h U Z hclosed hg hh hs htrace r₀ hr₀
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
    simpa only [LinearEquiv.symm_apply_apply] using hE j (finiteEquiv.symm f)
  · intro i v
    rw [RowMultiplicationCoordinates.coordinate_apply,AmbientCovectorTransport.covector_dualCoordinates,
      LinearEquiv.symm_apply_apply]
    simpa only [LinearEquiv.symm_apply_apply] using hQ i (rowFiniteEquiv.symm v)
  · apply (ActualTraceMotion.eval_covectorMatrix_kernel_iff g lam x).mpr
    intro z
    simpa only [hr,lam,AmbientCovectorTransport.covector_dualCoordinates,LinearEquiv.symm_apply_apply]
      using hfirst z
  · change (ActualCorrectionMotion.finitePolynomialConstraint g h U sectionMap).map
      (eval (Sum.elim lam x)) *ᵥ y.1=0
    rw [ActualCorrectionMotion.finitePolynomialConstraint_mulVec]
    change ActualCorrectionMotion.constraint g h U sectionMap r lam *ᵥ
      ActualCorrectionMotion.motionEncode s=0
    apply (ActualCorrectionMotion.constraint_kernel_iff g h U sectionMap
      hsection r lam (ActualCorrectionMotion.motionEncode s)).mpr
    intro a ha
    simpa only [ActualCorrectionMotion.motionEncode,LinearMap.coe_mk,AddHom.coe_mk,
      LinearEquiv.symm_apply_apply,lam,AmbientCovectorTransport.covector_dualCoordinates]
      using hsecond ⟨a,ha⟩
  · intro j
    rw [AmbientCovectorTransport.covector_dualCoordinates]
    exact hZ j

end Quartic.ActualSlicedMotionAvoidance
