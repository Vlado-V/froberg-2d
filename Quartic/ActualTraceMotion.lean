module

public import Quartic.QuotientMotionRank
public import Quartic.TraceGeneric
public import Quartic.RowMultiplicationCoordinates
public import Quartic.SplitBlock22Coordinates
public import Quartic.TraceTranspose

@[expose] public section

/-!
Actual first-stage pure-motion constraints. A fixed section of pure cubic
multiplication parametrizes every (3,1) cycle polynomially in the mixed
columns. Its four coefficients descend to the full injective trace.
-/
noncomputable section
namespace Quartic.ActualTraceMotion
open Module MvPolynomial Matrix SplitMiddle31 BilinearCoefficientKernel BilinearCovectorCharts
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {m c : ℕ}

abbrev PureCoefficients (K : Type*) [Field K] (m : ℕ) := Fin 4 → Fin m → Forms K 3 1
abbrev CycleParameters (K : Type*) [Field K] (m c : ℕ) :=
  (Fin c → Forms K 3 2) × LinearMap.ker (pureMultiplication (K := K) (m := m))

instance cycleParametersFree : Module.Free K (CycleParameters K m c) :=
  Module.Free.of_divisionRing K (CycleParameters K m c)

theorem pureMultiplication_surjective :
    Function.Surjective (pureMultiplication (K := K) (m := m)) := by
  intro y
  choose b hb using fun l => pureCubic_surjective (K := K) (y l)
  exact ⟨fun i l => b l i, funext hb⟩

def pureSection : Target K m →ₗ[K] PureCoefficients K m :=
  Classical.choose ((pureMultiplication (K := K) (m := m)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr pureMultiplication_surjective))

@[simp] theorem pureSection_apply (y : Target K m) :
    pureMultiplication (pureSection y) = y := by
  have h := Classical.choose_spec
    ((pureMultiplication (K := K) (m := m)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr pureMultiplication_surjective))
  exact LinearMap.congr_fun h y

/-- A fixed-domain linear parametrization of all actual cycles. -/
def cycleParameter (g : Mixed K m c) : CycleParameters K m c →ₗ[K] Source K m c where
  toFun x := (x.1, x.2.val - pureSection (mixedMultiplication g x.1))
  map_add' x y := by ext <;> simp [sub_add_sub_comm]
  map_smul' t x := by ext <;> simp [smul_sub]

@[simp] theorem cycleParameter_mem (g : Mixed K m c) (x : CycleParameters K m c) :
    multiplication g (cycleParameter g x) = 0 := by
  change mixedMultiplication g x.1 + pureMultiplication
    (x.2.val - pureSection (mixedMultiplication g x.1)) = 0
  rw [map_sub, x.2.property, pureSection_apply]
  simp only [zero_sub,add_neg_cancel]

def cycleLift (g : Mixed K m c) : CycleParameters K m c →ₗ[K] LinearMap.ker (multiplication g) :=
  (cycleParameter g).codRestrict _ (cycleParameter_mem g)

theorem cycleLift_surjective (g : Mixed K m c) : Function.Surjective (cycleLift g) := by
  intro a
  let z : LinearMap.ker (pureMultiplication (K := K) (m := m)) :=
    ⟨a.val.2 + pureSection (mixedMultiplication g a.val.1), by
      change pureMultiplication (a.val.2 + pureSection (mixedMultiplication g a.val.1)) = 0
      rw [map_add,pureSection_apply]
      have h := a.property
      change mixedMultiplication g a.val.1 + pureMultiplication a.val.2 = 0 at h
      exact (add_comm _ _).trans h⟩
  refine ⟨(a.val.1,z),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change a.val.2 + pureSection (mixedMultiplication g a.val.1) -
      pureSection (mixedMultiplication g a.val.1) = a.val.2
    exact add_sub_cancel_right _ _

/-- The four actual pure-motion coefficients of a cycle. -/
def rawCoefficients (g : Mixed K m c) : CycleParameters K m c →ₗ[K] PureCoefficients K m :=
  (LinearMap.snd K _ _).comp (cycleParameter g)

def cycleClassProjection {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (D : Submodule K V) :
    f.ker →ₗ[K] KernelModulo f D := (kernelBoundary f D).mkQ

private theorem cycleClassProjection_surjective {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (D : Submodule K V) :
    Function.Surjective (cycleClassProjection f D) := Submodule.mkQ_surjective _

/-- Every homology class has an actual cycle in the fixed parametrization. -/
def homologyParameter (g : Mixed K m c) : CycleParameters K m c →ₗ[K] Homology g :=
  (cycleClassProjection (multiplication g) (LinearMap.range (boundary g))).comp (cycleLift g)

theorem homologyParameter_surjective (g : Mixed K m c) : Function.Surjective (homologyParameter g) :=
  (cycleClassProjection_surjective _ _).comp (cycleLift_surjective g)

@[simp] theorem trace_homologyParameter (g : Mixed K m c) (x : CycleParameters K m c) :
    trace g (homologyParameter g x) =
      CoefficientConstraintRank.repeated (mixedSpace g).mkQ (rawCoefficients g x) := rfl

section Coordinates
variable {a b T : ℕ}
variable (e : (Fin m → Forms K 3 1) ≃ₗ[K] (Fin a → K))

def coordinateMixedSpace (g : Mixed K m c) : Submodule K (Fin a → K) :=
  (mixedSpace g).map e.toLinearMap

def quotientCoordinates (g : Mixed K m c) :
    ((Fin m → Forms K 3 1) ⧸ mixedSpace g) ≃ₗ[K]
      ((Fin a → K) ⧸ coordinateMixedSpace e g) :=
  Submodule.Quotient.equiv _ _ e rfl

def coordinateTrace (g : Mixed K m c) :
    Homology g →ₗ[K] (Fin 4 → ((Fin a → K) ⧸ coordinateMixedSpace e g)) :=
  (CoefficientConstraintRank.repeated (quotientCoordinates e g).toLinearMap).comp (trace g)

theorem coordinateTrace_injective (g : Mixed K m c)
    (hg : Function.Injective (mixedMultiplication g)) : Function.Injective (coordinateTrace e g) := by
  intro x y h
  apply trace_injective g hg
  funext i
  apply (quotientCoordinates e g).injective
  exact congrFun h i

def coordinateRaw (g : Mixed K m c) : CycleParameters K m c →ₗ[K] (Fin 4 → Fin a → K) :=
  (CoefficientConstraintRank.repeated e.toLinearMap).comp (rawCoefficients g)

@[simp] theorem coordinateTrace_homologyParameter (g : Mixed K m c) (x : CycleParameters K m c) :
    coordinateTrace e g (homologyParameter g x) =
      CoefficientConstraintRank.repeated (coordinateMixedSpace e g).mkQ (coordinateRaw e g x) := rfl

/-- Quotient coefficients of the actual raw cycles are exactly the full trace image. -/
theorem quotient_raw_range (g : Mixed K m c) :
    (LinearMap.range (coordinateRaw e g)).map
      (CoefficientConstraintRank.repeated (coordinateMixedSpace e g).mkQ) =
      LinearMap.range (coordinateTrace e g) := by
  apply le_antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨homologyParameter g x,coordinateTrace_homologyParameter e g x⟩
  · rintro _ ⟨x,rfl⟩
    obtain ⟨p,rfl⟩ := homologyParameter_surjective g x
    exact ⟨coordinateRaw e g p,⟨p,rfl⟩,(coordinateTrace_homologyParameter e g p).symm⟩

/-- Fixed, finite spanning columns; they may have redundant quotient images. -/
def columns (g : Mixed K m c) :
    Fin (finrank K (CycleParameters K m c)) → Fin 4 → Fin a → K :=
  fun j => coordinateRaw e g (Module.finBasis K (CycleParameters K m c) j)

theorem span_columns (g : Mixed K m c) :
    Submodule.span K (Set.range (columns e g)) = LinearMap.range (coordinateRaw e g) := by
  change Submodule.span K (Set.range ((coordinateRaw e g) ∘ Module.finBasis K (CycleParameters K m c))) = _
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top]

theorem quotient_columns_finrank (g : Mixed K m c)
    (hg : Function.Injective (mixedMultiplication g)) :
    finrank K ((Submodule.span K (Set.range (columns e g))).map
      (CoefficientConstraintRank.repeated (coordinateMixedSpace e g).mkQ)) = 2*m+2*c := by
  rw [span_columns,quotient_raw_range,LinearMap.finrank_range_of_inj
    (coordinateTrace_injective e g hg),homology_finrank]

variable (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))

/-- The literal first-stage matrix on the four child-quadratic motions. -/
def constraint (g : Mixed K m c) (ell : Fin T → K) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (Fin 4 × Fin b) K :=
  BilinearMotionConstraints.constraint mu ell (columns e g)

theorem constraint_smul (g : Mixed K m c) (ell : Fin T → K) (t : K) :
    constraint e mu g (t • ell) = t • constraint e mu g ell := by
  ext j z
  simp only [constraint,BilinearMotionConstraints.constraint,covector_smul,
    LinearMap.smul_apply,Matrix.smul_apply]

/-- The rank loses four times the true quotient kernel dimension, with no
additional presentation-dimension penalty. -/
theorem constraint_rank_bound (g : Mixed K m c)
    (hg : Function.Injective (mixedMultiplication g)) (ell : Fin T → K)
    (Rbar : ((Fin a → K) ⧸ coordinateMixedSpace e g) →ₗ[K] (Fin b → K))
    (hcomm : Rbar.comp (coordinateMixedSpace e g).mkQ = relationMap mu ell)
    {d : ℕ} (hker : finrank K (LinearMap.ker Rbar) ≤ d) :
    2*m+2*c-4*d ≤ (constraint e mu g ell).rank := by
  have h := QuotientMotionRank.constraint_rank_bound mu ell (coordinateMixedSpace e g)
    Rbar hcomm hker (columns e g)
  rw [quotient_columns_finrank e g hg] at h
  exact h


/-- Presentation annihilation is precisely enough for the actual relation
map to descend to the mixed quotient. -/
theorem presentation_le_relation_kernel (g : Mixed K m c) (ell : Fin T → K)
    (hE : ∀ j f, covector ell (mu f (e (g j))) = 0) :
    coordinateMixedSpace e g ≤ LinearMap.ker (relationMap mu ell) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact (relationMap_kernel_iff mu ell (e (g j))).mpr (hE j)

def descendedRelation (g : Mixed K m c) (ell : Fin T → K)
    (hE : ∀ j f, covector ell (mu f (e (g j))) = 0) :
    ((Fin a → K) ⧸ coordinateMixedSpace e g) →ₗ[K] (Fin b → K) :=
  (coordinateMixedSpace e g).liftQ (relationMap mu ell)
    (presentation_le_relation_kernel e mu g ell hE)

/-- Canonical quotient-aware first-stage rank, using the actual descended
covector relation and the actual trace-injectivity hypothesis. -/
theorem actual_rank_bound (g : Mixed K m c)
    (hg : Function.Injective (mixedMultiplication g)) (ell : Fin T → K)
    (hE : ∀ j f, covector ell (mu f (e (g j))) = 0)
    {d : ℕ} (hker : finrank K (LinearMap.ker (descendedRelation e mu g ell hE)) ≤ d) :
    2*m+2*c-4*d ≤ (constraint e mu g ell).rank := by
  apply constraint_rank_bound e mu g hg ell (descendedRelation e mu g ell hE) _ hker
  ext v
  rfl

/-- The matrix tests all actual cycle coefficients, not just a selected
family of homology representatives. -/
theorem constraint_kernel_iff (g : Mixed K m c) (ell : Fin T → K)
    (p : Fin 4 × Fin b → K) :
    constraint e mu g ell *ᵥ p = 0 ↔
      ∀ x : CycleParameters K m c,
        covector ell (∑ i : Fin 4, mu (fun f => p (i,f)) (coordinateRaw e g x i)) = 0 := by
  rw [constraint,BilinearMotionConstraints.kernel_iff,span_columns]
  constructor
  · intro h x
    exact h _ ⟨x,rfl⟩
  · intro h y hy
    obtain ⟨x,rfl⟩ := hy
    exact h x

section Polynomial
variable {I : Type*} (g : (I → K) → Mixed K m c) (hg : IsPolynomialFamily g)

include hg in
theorem rawCoefficients_polynomial (x : CycleParameters K m c) :
    IsPolynomialFamily (fun p => rawCoefficients (g p) x) := by
  let L : Mixed K m c →ₗ[K] Target K m :=
    (LinearMap.applyₗ (R := K) (M₂ := Target K m) x.1).comp TraceGeneric.mixedMultiplicationLinear
  have h := (isPolynomialFamily_const x.2.val).add (hg.linear_comp ((-pureSection).comp L))
  simpa only [rawCoefficients,cycleParameter,LinearMap.comp_apply,LinearMap.snd_apply,
    LinearMap.coe_mk,AddHom.coe_mk,LinearMap.neg_apply,sub_eq_add_neg,L,
    LinearMap.applyₗ,LinearMap.applyₗ',TraceGeneric.mixedMultiplicationLinear] using h

include hg in
theorem columns_polynomial (j : Fin (finrank K (CycleParameters K m c))) (i : Fin 4) (v : Fin a) :
    IsPolynomialFamily (fun p => columns e (g p) j i v) := by
  exact (((rawCoefficients_polynomial g hg (Module.finBasis K (CycleParameters K m c) j)).linear_comp
    (CoefficientConstraintRank.repeated e.toLinearMap)).linear_comp
      (LinearMap.proj i)).linear_comp (LinearMap.proj v)

/-- Literal polynomial entries of the fixed spanning coefficient columns. -/
def polynomialColumns (j : Fin (finrank K (CycleParameters K m c))) (i : Fin 4) (v : Fin a) :
    MvPolynomial I K :=
  Classical.choose (columns_polynomial e g hg j i v LinearMap.id)

@[simp] theorem eval_polynomialColumns (p : I → K)
    (j : Fin (finrank K (CycleParameters K m c))) (i : Fin 4) (v : Fin a) :
    eval p (polynomialColumns e g hg j i v) = columns e (g p) j i v :=
  Classical.choose_spec (columns_polynomial e g hg j i v LinearMap.id) p

def polynomialConstraint (ell : Fin T → MvPolynomial I K) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (Fin 4 × Fin b) (MvPolynomial I K) :=
  BilinearMotionConstraints.polynomialConstraint mu ell (polynomialColumns e g hg)

/-- Evaluation gives exactly the actual first-stage motion matrix. -/
theorem eval_polynomialConstraint (ell : Fin T → MvPolynomial I K) (p : I → K) :
    (polynomialConstraint e mu g hg ell).map (eval p) =
      constraint e mu (g p) (fun k => eval p (ell k)) := by
  rw [polynomialConstraint,BilinearMotionConstraints.eval_polynomialConstraint]
  simp only [eval_polynomialColumns,constraint]

end Polynomial


/-- Finite motion indexing shared with the second-stage correction matrix. -/
abbrev MotionIndex (b : ℕ) := Fin (Fintype.card (Fin 4 × Fin b))

def motionUnflatten (x : MotionIndex b → K) : Fin 4 → Fin b → K :=
  fun i f => x (Fintype.equivFin (Fin 4 × Fin b) (i,f))

/-- Reindexing makes both matrix index types literal `Fin` types. -/
def finiteConstraint (g : Mixed K m c) (ell : Fin T → K) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (MotionIndex b) K :=
  (constraint e mu g ell).reindex (Equiv.refl _) (Fintype.equivFin (Fin 4 × Fin b))

@[simp] theorem finiteConstraint_rank (g : Mixed K m c) (ell : Fin T → K) :
    (finiteConstraint e mu g ell).rank = (constraint e mu g ell).rank :=
  Matrix.rank_reindex _ _ _

theorem finiteConstraint_smul (g : Mixed K m c) (ell : Fin T → K) (t : K) :
    finiteConstraint e mu g (t • ell) = t • finiteConstraint e mu g ell := by
  ext j z
  exact congrFun (congrFun (constraint_smul e mu g ell t) j)
    ((Fintype.equivFin (Fin 4 × Fin b)).symm z)

theorem finiteConstraint_mulVec (g : Mixed K m c) (ell : Fin T → K) (x : MotionIndex b → K) :
    finiteConstraint e mu g ell *ᵥ x =
      constraint e mu g ell *ᵥ (fun z => motionUnflatten x z.1 z.2) := by
  classical
  ext j
  apply Fintype.sum_equiv (Fintype.equivFin (Fin 4 × Fin b)).symm
  intro f
  simp [finiteConstraint,motionUnflatten,Matrix.reindex_apply]

/-- The canonical quotient-aware estimate in the finite motion indexing. -/
theorem finiteConstraint_rank_bound (g : Mixed K m c)
    (hg : Function.Injective (mixedMultiplication g)) (ell : Fin T → K)
    (hE : ∀ j f, covector ell (mu f (e (g j))) = 0)
    {d : ℕ} (hker : finrank K (LinearMap.ker (descendedRelation e mu g ell hE)) ≤ d) :
    2*m+2*c-4*d ≤ (finiteConstraint e mu g ell).rank := by
  rw [finiteConstraint_rank]
  exact actual_rank_bound e mu g hg ell hE hker


/-- Exact ambient-to-quotient kernel shift for the canonical descended map. -/
theorem descendedRelation_kernel_finrank (g : Mixed K m c) (ell : Fin T → K)
    (hE : ∀ j f, covector ell (mu f (e (g j))) = 0) :
    finrank K (LinearMap.ker (relationMap mu ell)) =
      finrank K (LinearMap.ker (descendedRelation e mu g ell hE)) +
      finrank K (coordinateMixedSpace e g) := by
  have heq : LinearMap.ker (relationMap mu ell) =
      (LinearMap.ker (descendedRelation e mu g ell hE)).comap (coordinateMixedSpace e g).mkQ := by
    rw [← LinearMap.ker_comp]
    rfl
  rw [heq]
  exact QuotientBilinearImage.finrank_preimage _ _

theorem coordinateMixedSpace_finrank (g : Mixed K m c) (hg : LinearIndependent K g) :
    finrank K (coordinateMixedSpace e g) = c := by
  rw [coordinateMixedSpace,LinearEquiv.finrank_map_eq,mixedSpace,finrank_span_eq_card hg]
  exact Fintype.card_fin c

/-- An ambient kernel upper bound shifts by the actual presentation dimension;
the resulting motion rank still loses only 4*d. -/
theorem finiteConstraint_rank_bound_of_ambient (g : Mixed K m c)
    (hgi : LinearIndependent K g) (hg : Function.Injective (mixedMultiplication g))
    (ell : Fin T → K) (hE : ∀ j f, covector ell (mu f (e (g j))) = 0)
    {d : ℕ} (hker : finrank K (LinearMap.ker (relationMap mu ell)) ≤ d+c) :
    2*m+2*c-4*d ≤ (finiteConstraint e mu g ell).rank := by
  apply finiteConstraint_rank_bound e mu g hg ell hE
  have h := descendedRelation_kernel_finrank e mu g ell hE
  rw [coordinateMixedSpace_finrank e g hgi] at h
  omega

section PolynomialFinite
variable {I : Type*} (g : (I → K) → Mixed K m c) (hg : IsPolynomialFamily g)

def finitePolynomialConstraint (ell : Fin T → MvPolynomial I K) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (MotionIndex b) (MvPolynomial I K) :=
  (polynomialConstraint e mu g hg ell).reindex (Equiv.refl _) (Fintype.equivFin (Fin 4 × Fin b))

theorem eval_finitePolynomialConstraint (ell : Fin T → MvPolynomial I K) (p : I → K) :
    (finitePolynomialConstraint e mu g hg ell).map (eval p) =
      finiteConstraint e mu (g p) (fun k => eval p (ell k)) := by
  ext j f
  exact congrFun (congrFun (eval_polynomialConstraint e mu g hg ell p) j)
    ((Fintype.equivFin (Fin 4 × Fin b)).symm f)

end PolynomialFinite

end Coordinates

section ActualRows
open RowMultiplicationCoordinates HomogeneousCoefficientCoordinates

/-- The two orientations encode exactly the same mixed polynomial. -/
theorem traceCoordinates_injective : Function.Injective (SplitBlock22.traceCoordinates (K := K) (m := m)) := by
  intro x y h
  apply SplitBlock22.mixedEmbedding_injective
  rw [← SplitBlock22.linearYEmbed_traceCoordinates x,← SplitBlock22.linearYEmbed_traceCoordinates y,h]

/-- Reorienting the actual mixed coefficients is a linear equivalence. -/
def rowTraceEquiv : Rows K m 1 ≃ₗ[K] (Fin m → Forms K 3 1) :=
  LinearMap.linearEquivOfInjective SplitBlock22.traceCoordinates traceCoordinates_injective (by
    simp only [Rows,Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,finrank_forms]
    simp only [Nat.choose_one_right]
    omega)

/-- Trace coefficients in the fixed monomial row coordinates of multiplication. -/
def rowCoordinates : (Fin m → Forms K 3 1) ≃ₗ[K] (Fin (RowCount m 1) → K) :=
  rowTraceEquiv.symm.trans rowFiniteEquiv

@[simp] theorem rowCoordinates_traceCoordinates (v : Rows K m 1) :
    rowCoordinates (SplitBlock22.traceCoordinates v) = rowFiniteEquiv v := by
  change rowFiniteEquiv (rowTraceEquiv.symm (rowTraceEquiv v)) = rowFiniteEquiv v
  rw [LinearEquiv.symm_apply_apply]

/-- The actual family in the orientation used by the (3,1) trace theorem. -/
def rowMixed (g : Fin c → Rows K m 1) : SplitMiddle31.Mixed K m c :=
  fun j => SplitBlock22.traceCoordinates (g j)

/-- Actual coefficient extraction equals the transposition used by the common open. -/
theorem rowMixed_eq_transpose (g : Fin c → Rows K m 1) :
    rowMixed g = SimultaneousBlockConditions.transposeMixed g := by
  funext j
  exact TraceTranspose.traceCoordinates_eq_transpose g j

/-- The existing simultaneous block conditions supply the exact trace
injectivity hypothesis used by the actual first-stage motion matrix. -/
theorem mixedMultiplication_injective_of_blockConditions {q : ℕ}
    (p : AugmentedGeneric.ParameterIndex m c q → K)
    (hp : SimultaneousBlockConditions.BlockConditions p) :
    Function.Injective (mixedMultiplication (rowMixed (AugmentedGeneric.coefficientMixed p))) := by
  rw [rowMixed_eq_transpose]
  exact hp.2.2.1

theorem coordinateMixedSpace_rows (g : Fin c → Rows K m 1) :
    coordinateMixedSpace rowCoordinates (rowMixed g) =
      Submodule.span K (Set.range (fun j => rowFiniteEquiv (g j))) := by
  rw [coordinateMixedSpace,mixedSpace,Submodule.map_span,← Set.range_comp]
  congr 2
  funext j
  exact rowCoordinates_traceCoordinates (g j)

/-- The literal four-motion matrix for actual row multiplication. -/
def rowConstraint (g : Fin c → Rows K m 1) (ell : Fin (RowCount m 3) → K) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (Fin 4 × Fin (FormCount m 2)) K :=
  constraint rowCoordinates coordinate (rowMixed g) ell

/-- Decode the common finite pure-motion parameters into four actual child quadrics. -/
def motionDecode (x : MotionIndex (FormCount m 2) → K) : Fin 4 → Forms K m 2 :=
  fun i => finiteEquiv.symm (motionUnflatten x i)


/-- Raw cycle coefficients returned to the actual row orientation. -/
def rawRows (g : Fin c → Rows K m 1) (x : CycleParameters K m c) : Fin 4 → Rows K m 1 :=
  fun i => rowTraceEquiv.symm (rawCoefficients (rowMixed g) x i)

/-- The first-stage matrix in finite indices shared by the correction stage. -/
def finiteRowConstraint (g : Fin c → Rows K m 1) (ell : Fin (RowCount m 3) → K) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (MotionIndex (FormCount m 2)) K :=
  finiteConstraint rowCoordinates coordinate (rowMixed g) ell

theorem finiteRowConstraint_smul (g : Fin c → Rows K m 1)
    (ell : Fin (RowCount m 3) → K) (t : K) :
    finiteRowConstraint g (t • ell) = t • finiteRowConstraint g ell :=
  finiteConstraint_smul rowCoordinates coordinate (rowMixed g) ell t

/-- Vanishing of the finite matrix means vanishing on the literal row products
of the four actual pure-motion quadrics with all actual cycle coefficients. -/
theorem finiteRowConstraint_kernel_iff (g : Fin c → Rows K m 1)
    (ell : Fin (RowCount m 3) → K) (x : MotionIndex (FormCount m 2) → K) :
    finiteRowConstraint g ell *ᵥ x = 0 ↔
      ∀ z : CycleParameters K m c,
        covector ell (rowFiniteEquiv (∑ i : Fin 4,
          multiplication (motionDecode x i) (rawRows g z i))) = 0 := by
  rw [finiteRowConstraint,finiteConstraint_mulVec,constraint_kernel_iff]
  apply forall_congr'
  intro z
  have hs : (∑ i : Fin 4, coordinate (motionUnflatten x i)
      (coordinateRaw rowCoordinates (rowMixed g) z i)) =
      rowFiniteEquiv (∑ i : Fin 4, multiplication (motionDecode x i) (rawRows g z i)) := by
    have hsum := map_sum (rowFiniteEquiv (K := K) (m := m) (d := 3)).toLinearMap.toAddMonoidHom
      (fun i : Fin 4 => multiplication (motionDecode x i) (rawRows g z i)) Finset.univ
    change rowFiniteEquiv (∑ i : Fin 4, multiplication (motionDecode x i) (rawRows g z i)) =
      ∑ i : Fin 4, rowFiniteEquiv (multiplication (motionDecode x i) (rawRows g z i)) at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coordinateRaw,LinearMap.comp_apply,CoefficientConstraintRank.repeated,
      LinearMap.pi_apply,LinearMap.proj_apply,LinearEquiv.coe_coe,coordinate_apply,rowCoordinates,
      LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,motionDecode,rawRows]
  change (covector ell (∑ i : Fin 4, coordinate (motionUnflatten x i)
    (coordinateRaw rowCoordinates (rowMixed g) z i)) = 0) ↔ _
  rw [hs]

/-- Actual first-stage quotient rank in fixed row coordinates. -/
theorem finiteRowConstraint_rank_bound (g : Fin c → Rows K m 1)
    (hg : Function.Injective (mixedMultiplication (rowMixed g)))
    (ell : Fin (RowCount m 3) → K)
    (hE : ∀ j f, covector ell (coordinate f (rowCoordinates (rowMixed g j))) = 0)
    {d : ℕ} (hker : finrank K (LinearMap.ker
      (descendedRelation rowCoordinates coordinate (rowMixed g) ell hE)) ≤ d) :
    2*m+2*c-4*d ≤ (finiteRowConstraint g ell).rank :=
  finiteConstraint_rank_bound rowCoordinates coordinate (rowMixed g) hg ell hE hker

/-- Polynomial first-stage motion matrix in the actual ambient covector variables. -/
def covectorMatrix (g : Fin c → Rows K m 1) :
    Matrix (Fin (finrank K (CycleParameters K m c))) (MotionIndex (FormCount m 2))
      (MvPolynomial (Fin (RowCount m 3)) K) :=
  finitePolynomialConstraint rowCoordinates coordinate (fun _ => rowMixed g)
    (isPolynomialFamily_const _) X

@[simp] theorem eval_covectorMatrix (g : Fin c → Rows K m 1)
    (ell : Fin (RowCount m 3) → K) :
    (covectorMatrix g).map (eval ell) = finiteRowConstraint g ell := by
  rw [covectorMatrix,eval_finitePolynomialConstraint]
  simp only [eval_X,finiteRowConstraint]

/-- The literal polynomial matrix obeys the λ-scaling required by the
projective slice-motion avoidance theorem. -/
theorem eval_covectorMatrix_smul (g : Fin c → Rows K m 1)
    (ell : Fin (RowCount m 3) → K) (t : K) :
    (covectorMatrix g).map (eval (t • ell)) = t • (covectorMatrix g).map (eval ell) := by
  rw [eval_covectorMatrix,eval_covectorMatrix,finiteRowConstraint_smul]

/-- The evaluated polynomial matrix has the actual quotient-aware rank bound. -/
theorem eval_covectorMatrix_rank_bound (g : Fin c → Rows K m 1)
    (hg : Function.Injective (mixedMultiplication (rowMixed g)))
    (ell : Fin (RowCount m 3) → K)
    (hE : ∀ j f, covector ell (coordinate f (rowCoordinates (rowMixed g j))) = 0)
    {d : ℕ} (hker : finrank K (LinearMap.ker
      (descendedRelation rowCoordinates coordinate (rowMixed g) ell hE)) ≤ d) :
    2*m+2*c-4*d ≤ ((covectorMatrix g).map (eval ell)).rank := by
  rw [eval_covectorMatrix]
  exact finiteRowConstraint_rank_bound g hg ell hE hker


/-- On an actual ambient kernel stratum, presentation independence removes
exactly c relation directions before the fourfold rank loss is measured. -/
theorem eval_covectorMatrix_rank_bound_of_ambient (g : Fin c → Rows K m 1)
    (hgi : LinearIndependent K g)
    (hg : Function.Injective (mixedMultiplication (rowMixed g)))
    (ell : Fin (RowCount m 3) → K)
    (hE : ∀ j f, covector ell (rowFiniteEquiv (multiplication f (g j))) = 0)
    {d : ℕ} (hker : finrank K (LinearMap.ker (relationMap coordinate ell)) ≤ d+c) :
    2*m+2*c-4*d ≤ ((covectorMatrix g).map (eval ell)).rank := by
  rw [eval_covectorMatrix]
  apply finiteConstraint_rank_bound_of_ambient rowCoordinates coordinate (rowMixed g)
    (hgi.map' SplitBlock22.traceCoordinates (LinearMap.ker_eq_bot.mpr traceCoordinates_injective)) hg ell
  · intro j f
    simpa only [rowMixed,rowCoordinates_traceCoordinates,coordinate_apply,
      LinearEquiv.symm_apply_apply] using hE j (finiteEquiv.symm f)
  · exact hker

/-- The polynomial first-stage equations test the actual pure-motion products. -/
theorem eval_covectorMatrix_kernel_iff (g : Fin c → Rows K m 1)
    (ell : Fin (RowCount m 3) → K) (x : MotionIndex (FormCount m 2) → K) :
    (covectorMatrix g).map (eval ell) *ᵥ x = 0 ↔
      ∀ z : CycleParameters K m c,
        covector ell (rowFiniteEquiv (∑ i : Fin 4,
          multiplication (motionDecode x i) (rawRows g z i))) = 0 := by
  rw [eval_covectorMatrix]
  exact finiteRowConstraint_kernel_iff g ell x

end ActualRows

end Quartic.ActualTraceMotion
