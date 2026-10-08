import Quartic.MovingMiddleCorrection
import Quartic.QuotientMotionRank
import Quartic.RowMultiplicationCoordinates

/-!
# Actual second-stage correction motion constraints

After fixing the mixed and child generators, a linear section of the
surjective middle map gives polynomial spanning columns for its moving
correction preimage. The columns depend affinely on the earlier pure
motions; no basis of the moving preimage is chosen.
-/
noncomputable section
namespace Quartic.ActualCorrectionMotion
open Module Matrix MvPolynomial MiddleCoordinates MovingMiddleCorrection
open HomologyCoordinates PolynomialBilinearCoordinates RowMultiplicationCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts CoefficientConstraintRank
variable {K : Type*} [Field K] {m c q : ℕ}
set_option maxHeartbeats 1000000

abbrev ChildSpace (h : Fin q → Forms K m 2) := Submodule.span K (Set.range h)
abbrev ChildQuotient (h : Fin q → Forms K m 2) := Forms K m 2 ⧸ ChildSpace h
abbrev MiddleTarget (h : Fin q → Forms K m 2) := ChildQuotient h × ChildQuotient h
abbrev Raw (K : Type*) [Field K] (m c : ℕ) := Fin c → MiddleCoordinates.Mixed K m
abbrev Pure (K : Type*) [Field K] (m : ℕ) := Fin 4 → Forms K m 2
abbrev PureIndex (m : ℕ) := Fin (Fintype.card (Fin 4 × Fin (FormCount m 2)))

/-- The shared first-stage monomial coordinates: four quadratic motions. -/
def pureCoordinates : Pure K m ≃ₗ[K] (PureIndex m → K) where
  toFun r j := HomogeneousCoefficientCoordinates.finiteEquiv
    (r ((Fintype.equivFin (Fin 4 × Fin (FormCount m 2))).symm j).1)
    ((Fintype.equivFin (Fin 4 × Fin (FormCount m 2))).symm j).2
  invFun x i := HomogeneousCoefficientCoordinates.finiteEquiv.symm
    (fun b => x (Fintype.equivFin (Fin 4 × Fin (FormCount m 2)) (i,b)))
  left_inv r := by
    funext i
    simp
  right_inv x := by
    funext j
    simp
  map_add' r s := by
    funext j
    simp
  map_smul' a r := by
    funext j
    simp


def middleMap (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :=
  MiddleCoordinates.quotientMap g (ChildSpace h)

abbrev ColumnSpace (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (markedU : Submodule K (ChildQuotient h)) :=
  LinearMap.ker (middleMap g h) × (markedU × BlockHomology K)
abbrev ColumnIndex (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (markedU : Submodule K (ChildQuotient h)) := Fin (finrank K (ColumnSpace g h markedU))

/-- A fixed section exists on the actual middle-surjectivity locus. -/
theorem exists_section (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (hs : Function.Surjective (middleMap g h)) :
    ∃ sectionMap : MiddleTarget h →ₗ[K] Raw K m c,
      (middleMap g h).comp sectionMap=LinearMap.id := by
  exact (middleMap g h).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)

/-- Actual spanning map: fixed middle cycles plus lifts of the moving trace. -/
def rawMap (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m) :
    ColumnSpace g h markedU →ₗ[K] Raw K m c :=
  (LinearMap.ker (middleMap g h)).subtype.coprod
    (sectionMap.comp (traceMap (fun i => (ChildSpace h).mkQ (r i)) markedU))

@[simp] theorem rawMap_apply (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m)
    (z : ColumnSpace g h markedU) :
    rawMap g h markedU sectionMap r z = z.1.val +
      sectionMap (traceMap (fun i => (ChildSpace h).mkQ (r i)) markedU z.2) := rfl

/-- The fixed-section columns span exactly the actual moving preimage. -/
theorem rawMap_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (hsection : (middleMap g h).comp sectionMap=LinearMap.id) (r : Pure K m) :
    (rawMap g h markedU sectionMap r).range =
      (traceSpace h r markedU).comap (middleMap g h) := by
  have hs (a : MiddleTarget h) : middleMap g h (sectionMap a)=a :=
    LinearMap.congr_fun hsection a
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    change middleMap g h (z.1.val + sectionMap _) ∈ traceSpace h r markedU
    rw [map_add,show middleMap g h z.1.val=0 from z.1.property,zero_add,hs]
    exact ⟨z.2,rfl⟩
  · intro a ha
    obtain ⟨b,hb⟩ := ha
    have hc : a-sectionMap (middleMap g h a) ∈ LinearMap.ker (middleMap g h) := by
      change middleMap g h _=0
      rw [map_sub,hs,sub_self]
    refine ⟨(⟨a-sectionMap (middleMap g h a),hc⟩,b),?_⟩
    rw [rawMap_apply,hb]
    exact sub_add_cancel _ _

/-- Linear dependence of the pure trace on the earlier four motions. -/
def pureTraceMotion (h : Fin q → Forms K m 2) (ξ : BlockHomology K) :
    Pure K m →ₗ[K] MiddleTarget h where
  toFun r := AugmentedMiddle.pureTrace (fun i => (ChildSpace h).mkQ (r i)) ξ
  map_add' r s := by
    apply Prod.ext <;> simp [AugmentedMiddle.pureTrace,smul_add,Finset.sum_add_distrib]
  map_smul' a r := by
    apply Prod.ext <;> simp [AugmentedMiddle.pureTrace,Finset.smul_sum,smul_smul,mul_comm]

/-- The fixed part of a column includes its middle cycle and marked trace. -/
def constantColumn (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (z : ColumnSpace g h markedU) : Raw K m c :=
  z.1.val + sectionMap (z.2.1.val,-z.2.1.val)

def movingColumn (h : Fin q → Forms K m 2)
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (ξ : BlockHomology K) :
    Pure K m →ₗ[K] Raw K m c := sectionMap.comp (pureTraceMotion h ξ)

theorem rawMap_affine (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m)
    (z : ColumnSpace g h markedU) :
    rawMap g h markedU sectionMap r z = constantColumn g h markedU sectionMap z +
      movingColumn h sectionMap z.2.2 r := by
  rw [rawMap_apply]
  change z.1.val+sectionMap ((z.2.1.val,-z.2.1.val)+
    AugmentedMiddle.pureTrace (fun i => (ChildSpace h).mkQ (r i)) z.2.2)=_
  rw [map_add]
  change _ = (_ + _) + _
  exact (add_assoc _ _ _).symm

/-- Actual raw spanning columns in the fixed monomial coordinates of mixed rows. -/
def columns (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m) :
    ColumnIndex g h markedU → Fin c → Fin (RowCount m 1) → K :=
  fun j i => rowFiniteEquiv (rawMap g h markedU sectionMap r
    ((coordinates K _).symm (Pi.single j 1)) i)

/-- Literal affine polynomial coordinates for the moving correction columns. -/
def polynomialColumns (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) :
    ColumnIndex g h markedU → Fin c → Fin (RowCount m 1) → MvPolynomial (PureIndex m) K :=
  fun j i v =>
    let z := (coordinates K (ColumnSpace g h markedU)).symm (Pi.single j 1)
    C (rowFiniteEquiv (constantColumn g h markedU sectionMap z i) v) +
      polynomialOfLinear (((LinearMap.proj v).comp rowFiniteEquiv.toLinearMap).comp
        ((LinearMap.proj i).comp ((movingColumn h sectionMap z.2.2).comp
          (pureCoordinates (K := K) (m := m)).symm.toLinearMap)))

@[simp] theorem eval_polynomialColumns (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : PureIndex m → K)
    (j : ColumnIndex g h markedU) (i : Fin c) (v : Fin (RowCount m 1)) :
    eval r (polynomialColumns g h markedU sectionMap j i v)=
      columns g h markedU sectionMap (pureCoordinates.symm r) j i v := by
  simp only [polynomialColumns,map_add,eval_C,eval_polynomialOfLinear,
    LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe,columns,rawMap_affine,
    Pi.add_apply,map_add]

/-- The coordinate columns span the actual raw preimage, transported only by
fixed row-coordinate equivalences. -/
theorem columns_span (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (hsection : (middleMap g h).comp sectionMap=LinearMap.id) (r : Pure K m) :
    Submodule.span K (Set.range (columns g h markedU sectionMap r)) =
      ((traceSpace h r markedU).comap (middleMap g h)).map
        (repeated rowFiniteEquiv.toLinearMap) := by
  let e := coordinates K (ColumnSpace g h markedU)
  have hb : Submodule.span K (Set.range (fun j => e.symm (Pi.single j 1))) = ⊤ := by
    let b := (Pi.basisFun K (Fin (finrank K (ColumnSpace g h markedU)))).map e.symm
    have he : (fun j => e.symm (Pi.single j 1)) = b := by
      funext j
      simpa only [b,Pi.basisFun_apply] using
        ((Pi.basisFun K (Fin (finrank K (ColumnSpace g h markedU)))).map_apply e.symm j).symm
    rw [he]
    exact b.span_eq
  have he : columns g h markedU sectionMap r =
      (repeated rowFiniteEquiv.toLinearMap).comp (rawMap g h markedU sectionMap r) ∘
        (fun j => e.symm (Pi.single j 1)) := rfl
  rw [he,Set.range_comp,← Submodule.map_span,hb,Submodule.map_top,
    LinearMap.range_comp,rawMap_range g h markedU sectionMap hsection r]

/-- The source relation evaluated in actual mixed rows and fixed quadratic coordinates. -/
def sourceRelation (ell : Fin (RowCount m 3) → K) :
    MiddleCoordinates.Mixed K m →ₗ[K] (Fin (FormCount m 2) → K) :=
  (relationMap RowMultiplicationCoordinates.coordinate ell).comp rowFiniteEquiv.toLinearMap

/-- The actual second-stage scalar equations on c arbitrary quadratic motions. -/
def constraint (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) :=
  BilinearMotionConstraints.constraint RowMultiplicationCoordinates.coordinate ell
    (columns g h markedU sectionMap r)

/-- This rank is the actual repeated ambient relation image of the moving
correction preimage, not a model rank or an independent-motion assumption. -/
theorem constraint_rank_eq (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (hsection : (middleMap g h).comp sectionMap=LinearMap.id) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) :
    (constraint g h markedU sectionMap r ell).rank = finrank K
      (((traceSpace h r markedU).comap (middleMap g h)).map (repeated (sourceRelation ell))) := by
  rw [constraint,BilinearMotionConstraints.rank_eq,columns_span g h markedU sectionMap hsection r,
    ← Submodule.map_comp]
  congr 2

/-- Sharp correction rank under the actual augmented Good condition. The
only kernel dimension counted is that of the quotient relation. -/
theorem constraint_rank_bound (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (hsection : (middleMap g h).comp sectionMap=LinearMap.id) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) (d : ℕ)
    (Rbar : (MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) →ₗ[K]
      (Fin (FormCount m 2) → K))
    (hcomm : Rbar.comp (Submodule.span K (Set.range g)).mkQ=sourceRelation ell)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (AugmentedGeneric.quotientAugmented (AugmentedGeneric.productMap g) h r))
    (hs : Function.Surjective (middleMap g h)) :
    Counts.H m q c+3+finrank K markedU-(c:ℤ)*d ≤
      (constraint g h markedU sectionMap r ell).rank := by
  have hb := QuotientMotionRank.quotient_rank_bound_int
    (Submodule.span K (Set.range g)) (sourceRelation ell) Rbar hcomm hker
    ((traceSpace h r markedU).comap (middleMap g h))
  have he : (((traceSpace h r markedU).comap (middleMap g h)).map
      (repeated (Submodule.span K (Set.range g)).mkQ)) = coefficientImage g h r markedU := rfl
  rw [he,coefficientImage_finrank g h r hg hh ha hs markedU] at hb
  rw [constraint_rank_eq g h markedU sectionMap hsection r ell]
  exact hb

/-- Ambient and actual-row relation kernels have identical dimension. -/
theorem sourceRelation_kernel_finrank (ell : Fin (RowCount m 3) → K) :
    finrank K (LinearMap.ker (sourceRelation ell)) =
      finrank K (LinearMap.ker (relationMap RowMultiplicationCoordinates.coordinate ell)) := by
  have hr : (sourceRelation ell).range =
      (relationMap RowMultiplicationCoordinates.coordinate ell).range := by
    exact LinearMap.range_comp_of_range_eq_top _ rowFiniteEquiv.range
  have h₁ := (sourceRelation ell).finrank_range_add_finrank_ker
  have h₂ := (relationMap (RowMultiplicationCoordinates.coordinate (K := K) (m := m)) ell).finrank_range_add_finrank_ker
  have hd : finrank K (MiddleCoordinates.Mixed K m) =
      finrank K (Fin (RowCount m 1) → K) :=
    (rowFiniteEquiv (K := K) (m := m) (d := 1)).finrank_eq
  rw [hr] at h₁
  omega

/-- The kernel bound comes from the fixed ambient relation threshold and
independence of g, without choosing quotient coordinates. -/
theorem descended_kernel_bound (g : Fin c → MiddleCoordinates.Mixed K m)
    (ell : Fin (RowCount m 3) → K)
    (hE : Submodule.span K (Set.range g) ≤ LinearMap.ker (sourceRelation ell))
    (hg : LinearIndependent K g) (d : ℕ)
    (hambient : finrank K (LinearMap.ker
      (relationMap RowMultiplicationCoordinates.coordinate ell)) ≤ c+d) :
    finrank K (LinearMap.ker ((Submodule.span K (Set.range g)).liftQ (sourceRelation ell) hE)) ≤ d := by
  let E := Submodule.span K (Set.range g)
  let Rbar := E.liftQ (sourceRelation ell) hE
  have hc : Rbar.comp E.mkQ=sourceRelation ell := by ext x; rfl
  have hk := QuotientBilinearImage.finrank_preimage E (LinearMap.ker Rbar)
  rw [← LinearMap.ker_comp,hc,sourceRelation_kernel_finrank] at hk
  have he : finrank K E=c := by simpa only [Fintype.card_fin] using finrank_span_eq_card hg
  change finrank K (LinearMap.ker Rbar) ≤ d
  omega

/-- Sharp rank for the actual correction matrix, stated entirely using a
fixed ambient kernel threshold and the actual Good hypotheses. -/
theorem constraint_rank_bound_ambient (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (hsection : (middleMap g h).comp sectionMap=LinearMap.id) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) (d : ℕ)
    (hE : Submodule.span K (Set.range g) ≤ LinearMap.ker (sourceRelation ell))
    (hambient : finrank K (LinearMap.ker
      (relationMap RowMultiplicationCoordinates.coordinate ell)) ≤ c+d)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (AugmentedGeneric.quotientAugmented (AugmentedGeneric.productMap g) h r))
    (hs : Function.Surjective (middleMap g h)) :
    Counts.H m q c+3+finrank K markedU-(c:ℤ)*d ≤
      (constraint g h markedU sectionMap r ell).rank := by
  apply constraint_rank_bound g h markedU sectionMap hsection r ell d
    ((Submodule.span K (Set.range g)).liftQ (sourceRelation ell) hE)
    (by ext x; rfl) (descended_kernel_bound g ell hE hg d hambient) hg hh ha hs

/-- The kernel equations test the literal sum of mixed-coefficient products
on the full moving correction preimage. -/
theorem constraint_kernel_iff (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (hsection : (middleMap g h).comp sectionMap=LinearMap.id) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) (p : Fin c × Fin (FormCount m 2) → K) :
    constraint g h markedU sectionMap r ell *ᵥ p=0 ↔
      ∀ a ∈ (traceSpace h r markedU).comap (middleMap g h),
        covector ell (rowFiniteEquiv (∑ i : Fin c,
          RowMultiplicationCoordinates.multiplication
            (HomogeneousCoefficientCoordinates.finiteEquiv.symm (fun b => p (i,b))) (a i)))=0 := by
  rw [constraint,BilinearMotionConstraints.kernel_iff,
    columns_span g h markedU sectionMap hsection r]
  constructor
  · intro h a ha
    have hx := h _ ⟨a,ha,rfl⟩
    simpa only [repeated_apply,LinearEquiv.coe_coe,RowMultiplicationCoordinates.coordinate_apply,
      LinearEquiv.symm_apply_apply,← map_sum] using hx
  · intro h x hx
    obtain ⟨a,ha,rfl⟩ := hx
    simpa only [repeated_apply,LinearEquiv.coe_coe,RowMultiplicationCoordinates.coordinate_apply,
      LinearEquiv.symm_apply_apply,← map_sum] using h a ha

/-- Monomial coordinates of the actual c quadratic second-stage motions. -/
def motionEncode : (Fin c → Forms K m 2) →ₗ[K] (Fin c × Fin (FormCount m 2) → K) where
  toFun p z := HomogeneousCoefficientCoordinates.finiteEquiv (p z.1) z.2
  map_add' p q := by ext z; simp
  map_smul' a p := by ext z; simp

/-- The actual correction constraint as a linear map on quadratic motions.
This is suitable for appending an independent auxiliary covector block. -/
def constraintLinear (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) :
    (Fin c → Forms K m 2) →ₗ[K] (ColumnIndex g h markedU → K) :=
  (constraint g h markedU sectionMap r ell).mulVecLin.comp motionEncode

theorem motionEncode_surjective : Function.Surjective (motionEncode (K := K) (m := m) (c := c)) := by
  intro x
  refine ⟨fun i => HomogeneousCoefficientCoordinates.finiteEquiv.symm (fun b => x (i,b)),?_⟩
  funext z
  exact congrFun (HomogeneousCoefficientCoordinates.finiteEquiv.apply_symm_apply (fun b => x (z.1,b))) z.2

theorem constraintLinear_rank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) :
    finrank K (LinearMap.range (constraintLinear g h markedU sectionMap r ell)) =
      (constraint g h markedU sectionMap r ell).rank := by
  rw [constraintLinear,LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr motionEncode_surjective)]
  rfl

/-- Each row is λ applied to the actual quadratic motion times its actual
mixed correction coefficient, summed over the c generators. -/
theorem constraintLinear_apply (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) (r : Pure K m)
    (ell : Fin (RowCount m 3) → K) (p : Fin c → Forms K m 2)
    (j : ColumnIndex g h markedU) :
    constraintLinear g h markedU sectionMap r ell p j =
      covector ell (rowFiniteEquiv (∑ i : Fin c,
        RowMultiplicationCoordinates.multiplication (p i)
          (rawMap g h markedU sectionMap r ((coordinates K _).symm (Pi.single j 1)) i))) := by
  change (constraint g h markedU sectionMap r ell *ᵥ motionEncode p) j=_
  rw [constraint,BilinearMotionConstraints.mulVec_apply]
  simp only [motionEncode,LinearMap.coe_mk,AddHom.coe_mk,RowMultiplicationCoordinates.coordinate_apply,columns,
    LinearEquiv.symm_apply_apply,← map_sum]

/-- Polynomial matrix in the covector and the earlier pure motions. -/
def polynomialConstraint (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) :
    Matrix (ColumnIndex g h markedU) (Fin c × Fin (FormCount m 2))
      (MvPolynomial (Fin (RowCount m 3) ⊕ PureIndex m) K) :=
  BilinearMotionConstraints.polynomialConstraint RowMultiplicationCoordinates.coordinate
    (fun i => X (Sum.inl i))
    (fun j i v => rename Sum.inr (polynomialColumns g h markedU sectionMap j i v))

@[simp] theorem eval_polynomialConstraint (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (ell : Fin (RowCount m 3) → K) (r : PureIndex m → K) :
    (polynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r)) =
      constraint g h markedU sectionMap (pureCoordinates.symm r) ell := by
  rw [polynomialConstraint,BilinearMotionConstraints.eval_polynomialConstraint]
  congr 1
  · funext i
    simp
  · funext j i v
    simp [eval_rename]

/-- Scaling only λ scales every second-stage equation and leaves the earlier
pure motions fixed. -/
theorem polynomialConstraint_scaling (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (a : K) (ell : Fin (RowCount m 3) → K) (r : PureIndex m → K) :
    (polynomialConstraint g h markedU sectionMap).map (eval (Sum.elim (a • ell) r)) =
      a • (polynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r)) := by
  rw [eval_polynomialConstraint,eval_polynomialConstraint]
  ext j z
  simp [constraint,BilinearMotionConstraints.constraint,covector_apply,Finset.mul_sum,mul_assoc]

/-- Fin-indexed second-stage motion coordinates, retaining the shared
first-stage PureIndex in the polynomial variable labels. -/
abbrev MotionIndex (m c : ℕ) := Fin (Fintype.card (Fin c × Fin (FormCount m 2)))

def finitePolynomialConstraint (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c) :
    Matrix (ColumnIndex g h markedU) (MotionIndex m c)
      (MvPolynomial (Fin (RowCount m 3) ⊕ PureIndex m) K) :=
  (polynomialConstraint g h markedU sectionMap).submatrix (Equiv.refl _)
    (Fintype.equivFin (Fin c × Fin (FormCount m 2))).symm

theorem finitePolynomialConstraint_rank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (ell : Fin (RowCount m 3) → K) (r : PureIndex m → K) :
    ((finitePolynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r))).rank =
      (constraint g h markedU sectionMap (pureCoordinates.symm r) ell).rank := by
  change (((polynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r))).submatrix
    (Equiv.refl _) (Fintype.equivFin _).symm).rank=_
  rw [Matrix.rank_submatrix,eval_polynomialConstraint]

theorem finitePolynomialConstraint_scaling (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (a : K) (ell : Fin (RowCount m 3) → K) (r : PureIndex m → K) :
    (finitePolynomialConstraint g h markedU sectionMap).map (eval (Sum.elim (a • ell) r)) =
      a • (finitePolynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r)) := by
  have hh := polynomialConstraint_scaling g h markedU sectionMap a ell r
  exact congrArg (fun M => M.submatrix (Equiv.refl _)
    (Fintype.equivFin (Fin c × Fin (FormCount m 2))).symm) hh

/-- Decoding the Fin-indexed second-stage motion vector. -/
def motionDecode (p : MotionIndex m c → K) : Fin c → Forms K m 2 :=
  fun i => HomogeneousCoefficientCoordinates.finiteEquiv.symm
    (fun b => p (Fintype.equivFin (Fin c × Fin (FormCount m 2)) (i,b)))

theorem finitePolynomialConstraint_mulVec (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (markedU : Submodule K (ChildQuotient h))
    (sectionMap : MiddleTarget h →ₗ[K] Raw K m c)
    (ell : Fin (RowCount m 3) → K) (r : PureIndex m → K) (p : MotionIndex m c → K) :
    (finitePolynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r)) *ᵥ p =
      constraintLinear g h markedU sectionMap (pureCoordinates.symm r) ell (motionDecode p) := by
  change (((polynomialConstraint g h markedU sectionMap).map (eval (Sum.elim ell r))).submatrix
    (Equiv.refl _) (Fintype.equivFin _).symm) *ᵥ p=_
  rw [Matrix.submatrix_mulVec_equiv,eval_polynomialConstraint]
  change _ = constraint g h markedU sectionMap (pureCoordinates.symm r) ell *ᵥ
    motionEncode (motionDecode p)
  have he : motionEncode (motionDecode p) =
      fun z : Fin c × Fin (FormCount m 2) => p (Fintype.equivFin _ z) := by
    funext z
    exact congrFun (HomogeneousCoefficientCoordinates.finiteEquiv.apply_symm_apply
      (fun b => p (Fintype.equivFin (Fin c × Fin (FormCount m 2)) (z.1,b)))) z.2
  rw [he]
  rfl

end Quartic.ActualCorrectionMotion
