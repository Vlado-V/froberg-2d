module

public import Quartic.ExtraCorrectionOmega
public import Quartic.ActualDeformationResponseOmega

@[expose] public section

/-! The actual trace-plus-correction response with one retained middle column. -/
noncomputable section
namespace Quartic.ActualMarkedSquareResponseOmega
open Module MvPolynomial MovingMiddleCorrectionOmega RowMultiplicationCoordinates
open ActualTraceMotion ActualDeformationResponseOmega
variable {K : Type*} [Field K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 1200000

/-- The second response on the actual correction quotient. -/
def correctionResponse (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2) : ExtraCorrectionOmega.Correction ω g h r z markedU →ₗ[K] J g h :=
  ∑ i : Fin c, (coefficientResponse g h (s i)).comp
    ((LinearMap.proj i).comp (ExtraCorrectionOmega.coefficientMap ω g h r z markedU))

/-- Evaluation on actual moving-preimage coefficients; changing the
representative by a mixed Koszul boundary leaves this value unchanged. -/
theorem correctionResponse_mk (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2)
    (a : (ExtraCorrectionOmega.extraSpace ω h r z markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    correctionResponse ω g h r z markedU s (Submodule.Quotient.mk a)=
      (Relations g h).mkQ (∑ i : Fin c,multiplication (s i) (a.val i)) := by
  simp only [correctionResponse,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,ExtraCorrectionOmega.coefficientMap_mk,coefficientProjection_apply,
    coefficientResponse_mk,map_sum]

abbrev Source (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :=
  SplitMiddle31.Homology (rowMixed g) × ExtraCorrectionOmega.Correction ω g h r z markedU

/-- The actual response N, ordered as trace homology then correction homology. -/
def response (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2) : Source ω g h r z markedU →ₗ[K] J g h :=
  (traceResponse g h r).coprod (correctionResponse ω g h r z markedU s)

@[simp] theorem response_apply (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2) (a : SplitMiddle31.Homology (rowMixed g))
    (b : ExtraCorrectionOmega.Correction ω g h r z markedU) :
    response ω g h r z markedU s (a,b)=traceResponse g h r a+correctionResponse ω g h r z markedU s b := rfl

/-- The exact response domain dimension, using actual correction and trace
homology dimensions on the explicit augmented Good locus. -/
theorem source_finrank (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (ExtraCorrectionOmega.augmented ω g h r z))
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    (finrank K (Source ω g h r z markedU) : ℤ)=
      (2*m+2*c:ℕ)+Counts.H m q c+4+finrank K markedU := by
  change (finrank K (SplitMiddle31.Homology (rowMixed g) × ExtraCorrectionOmega.Correction ω g h r z markedU):ℤ)=_
  rw [Module.finrank_prod,SplitMiddle31.homology_finrank,
    ExtraCorrectionOmega.correction_finrank ω g h r z ha hs markedU,
    ← (SplitBlock22.homologyEquiv g h hh).finrank_eq]
  push_cast
  rw [SplitBlock22.homology_finrank_eq_H g h hg hh hs]
  ring

/-- Literal common-covector exclusion in the fixed ambient cubic rows gives
maximal rank of N after the auxiliary columns are discarded. The columns
and the exclusion are explicit inputs supplied by the motion incidence step. -/
theorem maximal_rank_of_ambient_exclusion
    (g : Fin c → Rows K m 1) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2)
    (z : ExtraCorrectionOmega.ChildQuotient h × ExtraCorrectionOmega.ChildQuotient h)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (s : Fin c → Forms K m 2)
    (Z : Fin (finrank K (J g h)-finrank K (Source ω g h r z markedU)) → GeneralF13.Ambient K m)
    (hexclude : ∀ ell : GeneralF13.Ambient K m →ₗ[K] K,
      Relations g h ≤ LinearMap.ker ell →
      (∀ p : CycleParameters K m c,ell (∑ i : Fin 4,multiplication (r i) (rawRows g p i))=0) →
      (∀ a : (ExtraCorrectionOmega.extraSpace ω h r z markedU).comap
        (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))),
        ell (∑ i : Fin c,multiplication (s i) (a.val i))=0) →
      (∀ j,ell (Z j)=0) → ell=0) :
    finrank K (LinearMap.range (response ω g h r z markedU s)) =
      min (finrank K (Source ω g h r z markedU)) (finrank K (J g h)) := by
  apply AuxiliarySurjectivity.maximal_rank_of_covector_exclusion
    (response ω g h r z markedU s) (fun j => (Relations g h).mkQ (Z j))
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
  have hc : ∀ a : (ExtraCorrectionOmega.extraSpace ω h r z markedU).comap
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

end Quartic.ActualMarkedSquareResponseOmega
