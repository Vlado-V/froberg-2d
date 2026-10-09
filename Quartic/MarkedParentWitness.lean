module

public import Quartic.ActualMarkedSquareRankOmega
public import Quartic.MarkedSquareRankCount
public import Quartic.ActualSplitCokernel

@[expose] public section

/-! Convert the actual enlarged deformation response to the marked lower endpoint. -/
noncomputable section
namespace Quartic.MarkedParentWitness
open Module ActualDeformationColumnsOmega
variable {K : Type*} [Field K] [Infinite K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 1500000

theorem of_response_rank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (hchild : Function.Surjective (quadraticMultiplication h))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h))
    (hresponse : Counts.hTotal m q c+1 ≤
      (finrank K (ActualMarkedSquareResponseOmega.response ω g h r
        (ExtraCorrectionOmega.squareClass h ζ) U p).range : ℤ)) :
    MarkedLowerWitness K (3+m) (4+(c+q)) := by
  obtain ⟨ε,_,hi,hgain⟩ := ActualMarkedSquareRankOmega.exists_independent_rank_gain
    ω g h p r k ζ U hmarked hs hg hh
  let f := deformedFamily g h p r (Pi.single k (markedDirection ω)) ε
  have hsplit := ActualSplitCokernel.split_rank_eq g h hs hchild hh hcubic h13
  exact MarkedSquareRankCount.marked_of_gain f hi (SplitBlock22.mixedEmbedding ζ)
    _ _ hsplit hresponse hgain

theorem of_response_formula (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (hchild : Function.Surjective (quadraticMultiplication h))
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h))
    (hdim : (finrank K U:ℤ)=Counts.delta m q)
    (hpos : 0 < Counts.chi (3+m) (4+(c+q)))
    (hresponse : (finrank K (ActualMarkedSquareResponseOmega.response ω g h r
        (ExtraCorrectionOmega.squareClass h ζ) U p).range : ℤ)=
      min (((2*m+2*c:ℕ):ℤ)+Counts.H m q c+4+finrank K U) (Counts.j m q c)) :
    MarkedLowerWitness K (3+m) (4+(c+q)) := by
  apply of_response_rank ω g h p r k ζ U hmarked hg hh hs hchild hcubic h13
  rw [hresponse,hdim]
  have hsource : ((2*m+2*c:ℕ):ℤ)+Counts.H m q c+4+Counts.delta m q=
      Counts.hTotal m q c+1 := by
    unfold Counts.hTotal Counts.k31
    push_cast
    ring
  rw [hsource]
  have he := Counts.transfer_euler_identity m q c
  rw [show m+3=3+m by omega,show q+c+4=4+(c+q) by omega] at he
  omega

end Quartic.MarkedParentWitness
