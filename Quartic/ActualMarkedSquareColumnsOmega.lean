module

public import Quartic.ActualMarkedSquareResponseOmega
public import Quartic.ActualDeformationColumnsOmega
public import Quartic.MarkedRankTransfer

@[expose] public section

/-! Actual augmented-square columns for D.13. The retained square is a
mixed quadratic's square. Its scalar coordinate is part of the augmented
source, while the old child cycle representatives are unchanged. -/
noncomputable section
namespace Quartic.ActualMarkedSquareColumnsOmega
open Module MvPolynomial ActualSplitCokernel ActualDeformationColumnsOmega
open ActualDeformationResponseOmega
variable {K : Type*} [Field K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def square (ζ : MiddleCoordinates.Mixed K m) : Forms K (3+m) 4 :=
  mulQuadratic (SplitBlock22.mixedEmbedding ζ) (SplitBlock22.mixedEmbedding ζ)

theorem square_eq_target (ζ : MiddleCoordinates.Mixed K m) :
    square ζ = SplitBlock22.targetEmbedding (SplitBlock22.mixedProduct ζ ζ) := by
  apply Subtype.ext
  exact (SplitBlock22.mixedProduct_polynomial ζ ζ).symm

theorem square_mem_split_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (ζ : MiddleCoordinates.Mixed K m)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    square ζ ∈ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range := by
  obtain ⟨b,hb⟩ := SplitBlock22.multiplication_surjective g h hs (SplitBlock22.mixedProduct ζ ζ)
  refine ⟨SplitBlock22.sourceEmbedding b,?_⟩
  rw [SplitBlock22.full_multiplication_commutes,hb,←square_eq_target]

/-- Decompose an actual enlarged correction preimage into its square,
pure-cycle, and marked old-child-cycle contributions. -/
theorem trace_preimage_representatives (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2) (k : Fin q)
    (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (z : (ExtraCorrectionOmega.extraSpace ω h r (ExtraCorrectionOmega.squareClass h ζ) U).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    ∃ t : K, ∃ bx : (quadraticMultiplication (ThreeBlockModel.blockQuadrics (K := K))).ker,
    ∃ byCycle : (quadraticMultiplication h).ker,
      MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z.val =
        SplitBlock22.elimination (Submodule.span K (Set.range h))
          (t • (SplitBlock22.mixedProduct ζ ζ) + (pureFirstResponse r bx.val +
            childFirstResponse (Pi.single k (markedDirection ω)) byCycle.val)) := by
  have hz := z.property
  change ∃ u, ExtraTraceOmega.extraTrace ω (ExtraCorrectionOmega.squareClass h ζ)
    (fun i => (Submodule.span K (Set.range h)).mkQ (r i)) U u =
      MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z.val at hz
  obtain ⟨⟨t,u,ξ⟩,he⟩ := hz
  obtain ⟨bx,hbx⟩ := pure_class_surjective ξ
  obtain ⟨byCycle,hby⟩ := hmarked u
  refine ⟨t,bx,byCycle,?_⟩
  rw [map_add,map_smul,map_add,SplitBlock22.elimination_mixedProduct,
    pureFirstResponse_elimination,marked_child_elimination,hbx,hby,←he]
  change t • _ + MovingMiddleCorrectionOmega.traceMap ω _ U (u,ξ) =
    t • _ + (AugmentedMiddle.pureTrace _ ξ + (ω • u.val,-u.val))
  congr 1
  apply Prod.ext <;>
    simp only [MovingMiddleCorrectionOmega.traceMap_apply,Prod.fst_add,Prod.snd_add] <;> abel

/-- The square coordinate absorbs precisely the extra retained target term.
The remaining corrected source is an actual pure/child cycle. -/
theorem correction_response_realized (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (z : (ExtraCorrectionOmega.extraSpace ω h r (ExtraCorrectionOmega.squareClass h ζ) U).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    ∃ a b : (Fin (4+(c+q)) → Forms K (3+m) 2) × K,
      MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (square ζ) a = 0 ∧
      MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (square ζ) b = -MarkedRankTransfer.perturbation
          (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) a ∧
      projectionRawJ g h (MarkedRankTransfer.perturbation
          (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) b) =
        ActualMarkedSquareResponseOmega.correctionResponse ω g h r
          (ExtraCorrectionOmega.squareClass h ζ) U p (Submodule.Quotient.mk z) := by
  classical
  obtain ⟨t,bx,byCycle,hz⟩ := trace_preimage_representatives ω g h r k ζ U hmarked z
  let tr : SplitBlock22.Target K m := pureFirstResponse r bx.val +
    childFirstResponse (Pi.single k (markedDirection ω)) byCycle.val
  let a : Fin (4+(c+q)) → Forms K (3+m) 2 :=
    -(SplitBlock40.sourceEmbedding bx.val + sourceEmbedding04 byCycle.val)
  have ha : quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0 := by
    dsimp [a]
    rw [map_neg,map_add]
    have hx : quadraticMultiplication (SplitBlock22.fullGenerators g h)
        (SplitBlock40.sourceEmbedding bx.val) = 0 := by
      change quadraticMultiplication (SplitBlock31.generators
        (fun j => SplitBlock22.traceCoordinates (g j)) h) (SplitBlock40.sourceEmbedding bx.val) = 0
      rw [SplitBlock40.multiplication_commutes,bx.property,map_zero]
    rw [hx,multiplication_sourceEmbedding04,byCycle.property,map_zero,add_zero,neg_zero]
  have ht : quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))) a =
      -(SplitBlock22.targetEmbedding tr) := by
    dsimp [a,tr]
    rw [map_neg,map_add,firstVariation_pure,firstVariation_child,map_add]
  have hm : t • (SplitBlock22.mixedProduct ζ ζ) + tr - SplitBlock22.mixedMap g z.val ∈
      (SplitBlock22.elimination (Submodule.span K (Set.range h))).ker := by
    change SplitBlock22.elimination _ _ = 0
    rw [map_sub,SplitBlock22.elimination_mixedMap,←hz,sub_self]
  rw [SplitBlock22.elimination_ker_ranges,Submodule.mem_sup] at hm
  obtain ⟨v,⟨u,rfl⟩,w,⟨d,rfl⟩,he⟩ := hm
  let b : SplitBlock22.Source K m c q := (u,z.val,d)
  have hb : b.2.1 = z.val := rfl
  have hprod : SplitBlock22.multiplication g h b = t • (SplitBlock22.mixedProduct ζ ζ) + tr := by
    have he' := congrArg (fun x => x + SplitBlock22.mixedMap g z.val) he
    rw [sub_add_cancel] at he'
    change SplitBlock22.pureMap u + (SplitBlock22.mixedMap g z.val + SplitBlock22.childMap h d) = _
    calc
      _ = SplitBlock22.pureMap u + SplitBlock22.childMap h d + SplitBlock22.mixedMap g z.val := by abel
      _ = _ := he'
  have hfull : quadraticMultiplication (SplitBlock22.fullGenerators g h)
      (SplitBlock22.sourceEmbedding b) = t • (square ζ) + SplitBlock22.targetEmbedding tr := by
    rw [SplitBlock22.full_multiplication_commutes,hprod,map_add,map_smul,←square_eq_target]
  refine ⟨(a,0),(SplitBlock22.sourceEmbedding b,-t),?_,?_,?_⟩
  · simp only [MarkedRankTransfer.augmented_apply,ha,zero_smul,add_zero]
  · change quadraticMultiplication (SplitBlock22.fullGenerators g h) (SplitBlock22.sourceEmbedding b) +
      (-t) • (square ζ) = -quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))) a
    have hn : (-t) • (square ζ) = -(t • (square ζ)) := neg_smul t (square ζ)
    rw [hfull,ht,neg_neg,hn]
    abel
  · change (GeneralF13.combined g h).range.mkQ
      (projection13 (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))
        (SplitBlock22.sourceEmbedding b))) = _
    rw [firstVariation_middle,hb,ActualMarkedSquareResponseOmega.correctionResponse_mk]

theorem correction_class_realized (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (ξ : ExtraCorrectionOmega.Correction ω g h r (ExtraCorrectionOmega.squareClass h ζ) U) :
    ∃ a b : (Fin (4+(c+q)) → Forms K (3+m) 2) × K,
      MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (square ζ) a = 0 ∧
      MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (square ζ) b = -MarkedRankTransfer.perturbation
          (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) a ∧
      projectionRawJ g h (MarkedRankTransfer.perturbation
          (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) b) =
        ActualMarkedSquareResponseOmega.correctionResponse ω g h r
          (ExtraCorrectionOmega.squareClass h ζ) U p ξ := by
  induction ξ using Submodule.Quotient.induction_on with | H z =>
  exact correction_response_realized ω g h p r k ζ U hmarked z

/-- Exact realizations of the full enlarged response, in the source of the
literal multiplication pencil with its one fixed square column. -/
theorem response_realized (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (ξ : ActualMarkedSquareResponseOmega.Source ω g h r (ExtraCorrectionOmega.squareClass h ζ) U) :
    ∃ a b : (Fin (4+(c+q)) → Forms K (3+m) 2) × K,
      MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (square ζ) a = 0 ∧
      MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (square ζ) b = -MarkedRankTransfer.perturbation
          (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) a ∧
      projectionRawJ g h (MarkedRankTransfer.perturbation
          (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) b) =
        ActualMarkedSquareResponseOmega.response ω g h r
          (ExtraCorrectionOmega.squareClass h ζ) U p ξ := by
  obtain ⟨a₃,h₃,_,hr₃⟩ := trace_class_realized g h p r (Pi.single k (markedDirection ω)) ξ.1
  obtain ⟨a,b,ha,hb,hr⟩ := correction_class_realized ω g h p r k ζ U hmarked ξ.2
  have h₃aug : MarkedRankTransfer.augmented
      (quadraticMultiplication (SplitBlock22.fullGenerators g h)) (square ζ) (a₃,0) = 0 := by
    simp only [MarkedRankTransfer.augmented_apply,h₃,zero_smul,add_zero]
  refine ⟨a,b+(a₃,0),ha,?_,?_⟩
  · rw [map_add,hb,h₃aug,add_zero]
  · rw [map_add,map_add,hr]
    change _ + projectionRawJ g h
      (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))) a₃) = _
    rw [hr₃]
    exact add_comm _ _

end Quartic.ActualMarkedSquareColumnsOmega
