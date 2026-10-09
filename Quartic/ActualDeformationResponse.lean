module

public import Quartic.ActualCorrectionMotion
public import Quartic.ActualTraceMotion
public import Quartic.ActualSplitCokernel
public import Quartic.AuxiliarySurjectivity

@[expose] public section

/-!
# The actual two-stage deformation response

Both responses take values in the literal retained quotient
Ambient / range(combined g h). They descend through the already proved
trace and correction coefficient maps; all products of mixed relations
vanish in this quotient. No exhaustion of full source homology is used.
-/
noncomputable section
namespace Quartic.ActualDeformationResponse
open Module MvPolynomial RowMultiplicationCoordinates MovingMiddleCorrection
open ActualTraceMotion
variable {K : Type*} [Field K] {m c q : ℕ}
set_option maxHeartbeats 1000000

abbrev Relations (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2) :=
  (GeneralF13.combined g h).range
abbrev J (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2) := ActualSplitCokernel.RawJ g h
abbrev MixedSpace (g : Fin c → Rows K m 1) := Submodule.span K (Set.range g)

/-- An actual product of any quadratic with a mixed generator is already
a relation in the retained target quotient. -/
theorem product_generator_mem (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (f : Forms K m 2) (j : Fin c) : multiplication f (g j) ∈ Relations g h := by
  classical
  refine ⟨(Pi.single j f,0),?_⟩
  change GeneralF13.multiplication g (Pi.single j f) + GeneralF13.childMultiplication h 0 = _
  rw [map_zero,add_zero]
  funext r
  apply Subtype.ext
  simp only [GeneralF13.multiplication_val,multiplication_val,Pi.single_apply,
    apply_ite,ZeroMemClass.coe_zero,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact mul_comm _ _

/-- Every product of a child quadric with an actual mixed row is also a
relation in the retained target quotient. -/
theorem child_product_mem (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (i : Fin q) (v : Rows K m 1) : multiplication (h i) v ∈ Relations g h := by
  classical
  refine ⟨(0,Pi.single i v),?_⟩
  change GeneralF13.multiplication g 0 + GeneralF13.childMultiplication h (Pi.single i v)=_
  rw [map_zero,zero_add]
  funext r
  apply Subtype.ext
  change (CubicGeneric.cubicMap h (fun j => (Pi.single i v : Fin q → Rows K m 1) j r)).val=_
  simp only [CubicGeneric.cubicMap_val,Pi.single_apply,ite_apply,Pi.zero_apply,
    apply_ite,ZeroMemClass.coe_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true,multiplication_val]
  exact mul_comm _ _

/-- Multiplication into J kills the complete mixed generator subspace. -/
theorem mixedSpace_le_product_kernel (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (f : Forms K m 2) :
    MixedSpace g ≤ LinearMap.ker ((Relations g h).mkQ.comp (multiplication f)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr (product_generator_mem g h f j)

/-- Actual quadratic multiplication on one mixed coefficient quotient. -/
def coefficientResponse (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (f : Forms K m 2) : (Rows K m 1 ⧸ MixedSpace g) →ₗ[K] J g h :=
  (MixedSpace g).liftQ ((Relations g h).mkQ.comp (multiplication f))
    (mixedSpace_le_product_kernel g h f)

@[simp] theorem coefficientResponse_mk (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (f : Forms K m 2) (a : Rows K m 1) :
    coefficientResponse g h f ((MixedSpace g).mkQ a)=
      (Relations g h).mkQ (multiplication f a) := rfl

/-- Reorienting mixed rows transports exactly their actual relation span. -/
theorem traceSpace_map_rows (g : Fin c → Rows K m 1) :
    (SplitMiddle31.mixedSpace (rowMixed g)).map rowTraceEquiv.symm.toLinearMap=MixedSpace g := by
  rw [SplitMiddle31.mixedSpace,Submodule.map_span,← Set.range_comp]
  congr 2
  funext j
  change rowTraceEquiv.symm (rowTraceEquiv (g j))=g j
  exact rowTraceEquiv.symm_apply_apply _

def traceQuotientEquiv (g : Fin c → Rows K m 1) :
    ((Fin m → Forms K 3 1) ⧸ SplitMiddle31.mixedSpace (rowMixed g)) ≃ₗ[K]
      (Rows K m 1 ⧸ MixedSpace g) :=
  Submodule.Quotient.equiv _ _ rowTraceEquiv.symm (traceSpace_map_rows g)

@[simp] theorem traceQuotientEquiv_mk (g : Fin c → Rows K m 1) (a : Fin m → Forms K 3 1) :
    traceQuotientEquiv g ((SplitMiddle31.mixedSpace (rowMixed g)).mkQ a)=
      (MixedSpace g).mkQ (rowTraceEquiv.symm a) := rfl

/-- The first response on actual (3,1) homology. -/
def traceResponse (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2) : SplitMiddle31.Homology (rowMixed g) →ₗ[K] J g h :=
  ∑ i : Fin 4, (coefficientResponse g h (r i)).comp
    ((traceQuotientEquiv g).toLinearMap.comp
      ((LinearMap.proj i).comp (SplitMiddle31.trace (rowMixed g))))

/-- Evaluation on an actual cycle, with its actual four pure coefficients. -/
theorem traceResponse_mk (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2) (a : LinearMap.ker (SplitMiddle31.multiplication (rowMixed g))) :
    traceResponse g h r (Submodule.Quotient.mk a)=
      (Relations g h).mkQ (∑ i : Fin 4,multiplication (r i) (rowTraceEquiv.symm (a.val.2 i))) := by
  change (∑ i : Fin 4, coefficientResponse g h (r i)
    (traceQuotientEquiv g ((SplitMiddle31.mixedSpace (rowMixed g)).mkQ (a.val.2 i)))) = _
  simp only [traceQuotientEquiv_mk,coefficientResponse_mk,map_sum]

/-- The same first response on the fixed cycle parametrization used by the
actual first-stage polynomial matrix. -/
theorem traceResponse_homologyParameter (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2) (p : CycleParameters K m c) :
    traceResponse g h r (homologyParameter (rowMixed g) p)=
      (Relations g h).mkQ (∑ i : Fin 4,multiplication (r i) (rawRows g p i)) := by
  exact traceResponse_mk g h r (cycleLift (rowMixed g) p)

/-- The second response on the actual correction quotient. -/
def correctionResponse (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2) : Correction g h r markedU →ₗ[K] J g h :=
  ∑ i : Fin c, (coefficientResponse g h (s i)).comp
    ((LinearMap.proj i).comp (coefficientMap g h r markedU))

/-- Evaluation on actual moving-preimage coefficients; changing the
representative by a mixed Koszul boundary leaves this value unchanged. -/
theorem correctionResponse_mk (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2)
    (a : (traceSpace h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    correctionResponse g h r markedU s (Submodule.Quotient.mk a)=
      (Relations g h).mkQ (∑ i : Fin c,multiplication (s i) (a.val i)) := by
  simp only [correctionResponse,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,coefficientMap_mk,coefficientProjection_apply,
    coefficientResponse_mk,map_sum]

abbrev Source (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :=
  SplitMiddle31.Homology (rowMixed g) × Correction g h r markedU

/-- The actual response N, ordered as trace homology then correction homology. -/
def response (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2) : Source g h r markedU →ₗ[K] J g h :=
  (traceResponse g h r).coprod (correctionResponse g h r markedU s)

@[simp] theorem response_apply (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2) (a : SplitMiddle31.Homology (rowMixed g))
    (b : Correction g h r markedU) :
    response g h r markedU s (a,b)=traceResponse g h r a+correctionResponse g h r markedU s b := rfl

/-- The exact response domain dimension, using actual correction and trace
homology dimensions on the explicit augmented Good locus. -/
theorem source_finrank (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (AugmentedGeneric.quotientAugmented (AugmentedGeneric.productMap g) h r))
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    (finrank K (Source g h r markedU) : ℤ)=
      (2*m+2*c:ℕ)+Counts.H m q c+3+finrank K markedU := by
  have hc := coefficientImage_finrank g h r hg hh ha hs markedU
  rw [coefficientImage_eq_range,LinearMap.finrank_range_of_inj
    (coefficientMap_injective g h r hg ha markedU)] at hc
  change (finrank K (SplitMiddle31.Homology (rowMixed g) × Correction g h r markedU):ℤ)=_
  rw [Module.finrank_prod,SplitMiddle31.homology_finrank]
  push_cast
  omega

/-- Literal common-covector exclusion in the fixed ambient cubic rows gives
maximal rank of N after the auxiliary columns are discarded. The columns
and the exclusion are explicit inputs supplied by the motion incidence step. -/
theorem maximal_rank_of_ambient_exclusion
    (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2)
    (Z : Fin (finrank K (J g h)-finrank K (Source g h r markedU)) → GeneralF13.Ambient K m)
    (hexclude : ∀ ell : GeneralF13.Ambient K m →ₗ[K] K,
      Relations g h ≤ LinearMap.ker ell →
      (∀ p : CycleParameters K m c,ell (∑ i : Fin 4,multiplication (r i) (rawRows g p i))=0) →
      (∀ a : (traceSpace h r markedU).comap
        (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))),
        ell (∑ i : Fin c,multiplication (s i) (a.val i))=0) →
      (∀ j,ell (Z j)=0) → ell=0) :
    finrank K (LinearMap.range (response g h r markedU s)) =
      min (finrank K (Source g h r markedU)) (finrank K (J g h)) := by
  apply AuxiliarySurjectivity.maximal_rank_of_covector_exclusion
    (response g h r markedU s) (fun j => (Relations g h).mkQ (Z j))
  intro ell hN hZ
  let ambientEll := ell.comp (Relations g h).mkQ
  have hrel : Relations g h ≤ LinearMap.ker ambientEll := by
    intro a ha
    change ell ((Relations g h).mkQ a)=0
    have hz : (Relations g h).mkQ a=0 := (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [hz,map_zero]
  have ht : ∀ p : CycleParameters K m c,
      ambientEll (∑ i : Fin 4,multiplication (r i) (rawRows g p i))=0 := by
    intro p
    dsimp only [ambientEll,LinearMap.comp_apply]
    have hp := LinearMap.congr_fun hN (homologyParameter (rowMixed g) p,0)
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,response_apply,map_zero,add_zero,
      traceResponse_homologyParameter] using hp
  have hc : ∀ a : (traceSpace h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))),
      ambientEll (∑ i : Fin c,multiplication (s i) (a.val i))=0 := by
    intro a
    dsimp only [ambientEll,LinearMap.comp_apply]
    have hp := LinearMap.congr_fun hN (0,Submodule.Quotient.mk a)
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,response_apply,map_zero,zero_add,correctionResponse_mk] using hp
  have hzero := hexclude ambientEll hrel ht hc hZ
  apply LinearMap.ext
  intro a
  obtain ⟨b,rfl⟩ := (Relations g h).mkQ_surjective a
  exact LinearMap.congr_fun hzero b

end Quartic.ActualDeformationResponse
