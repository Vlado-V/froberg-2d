module

public import Quartic.ActualMarkedSquareColumnsOmega
public import Quartic.ActualDeformationRankOmega

@[expose] public section

/-! The actual augmented-square pencil gains the full enlarged response rank
on the same nonempty scalar open where the deformed generators are independent. -/
noncomputable section
namespace Quartic.ActualMarkedSquareRankOmega
open Module MvPolynomial ActualDeformationColumnsOmega ActualMarkedSquareColumnsOmega
variable {K : Type*} [Field K] [Infinite K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 1800000

/-- The retained target projection kills every initial augmented column. -/
theorem projection_annihilates (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (ζ : MiddleCoordinates.Mixed K m)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    (projectionRawJ g h).comp (MarkedRankTransfer.augmented
      (quadraticMultiplication (SplitBlock22.fullGenerators g h)) (square ζ)) = 0 :=
  MarkedRankTransfer.projection_annihilates _ _ (square_mem_split_range g h ζ hs) _
    (ActualDeformationRankOmega.projection_annihilates g h)

theorem rank_principal_open (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
          finrank K (ActualMarkedSquareResponseOmega.response ω g h r
            (ExtraCorrectionOmega.squareClass h ζ) U p).range ≤
          finrank K (MarkedRankTransfer.augmented
            (quadraticMultiplication (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε))
            (square ζ)).range := by
  obtain ⟨D,hD,hgain⟩ := DeformationRank.rank_gain_of_realizations_principal_open
    (MarkedRankTransfer.augmented (quadraticMultiplication (SplitBlock22.fullGenerators g h)) (square ζ))
    (MarkedRankTransfer.perturbation (quadraticMultiplication
      (motionFamily p r (Pi.single k (markedDirection ω)))))
    (projectionRawJ g h)
    (ActualMarkedSquareResponseOmega.response ω g h r (ExtraCorrectionOmega.squareClass h ζ) U p)
    (projection_annihilates g h ζ hs)
    (ActualMarkedSquareColumnsOmega.response_realized ω g h p r k ζ U hmarked)
  refine ⟨D,hD,?_⟩
  intro ε hε hDε
  have he := hgain ε hε hDε
  rw [MarkedRankTransfer.augmented_range_of_mem _ (square_mem_split_range g h ζ hs)] at he
  rw [deformed_multiplication,MarkedRankTransfer.pencil_eq]
  exact he

theorem independent_rank_principal_open (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        LinearIndependent K (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε) ∧
        finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
          finrank K (ActualMarkedSquareResponseOmega.response ω g h r
            (ExtraCorrectionOmega.squareClass h ζ) U p).range ≤
          finrank K (MarkedRankTransfer.augmented
            (quadraticMultiplication (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε))
            (square ζ)).range := by
  obtain ⟨D,hD,hRank⟩ := rank_principal_open ω g h p r k ζ U hmarked hs
  obtain ⟨E,hE,he⟩ := DeformationIndependence.principal_open g h p r (Pi.single k (markedDirection ω)) hg hh
  refine ⟨D*E,by simpa only [map_mul] using mul_ne_zero hD hE,?_⟩
  intro ε hε hDE
  have hne : eval (fun _ => ε) D ≠ 0 ∧ eval (fun _ => ε) E ≠ 0 := by
    apply mul_ne_zero_iff.mp
    simpa only [map_mul] using hDE
  exact ⟨he ε hne.2,hRank ε hε hne.1⟩

theorem exists_independent_rank_gain (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (ζ : MiddleCoordinates.Mixed K m)
    (U : Submodule K (ExtraCorrectionOmega.ChildQuotient h))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ ε : K, ε ≠ 0 ∧ LinearIndependent K
      (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε) ∧
      finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
        finrank K (ActualMarkedSquareResponseOmega.response ω g h r
          (ExtraCorrectionOmega.squareClass h ζ) U p).range ≤
        finrank K (MarkedRankTransfer.augmented
          (quadraticMultiplication (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε))
          (square ζ)).range := by
  obtain ⟨D,hD,h⟩ := independent_rank_principal_open ω g h p r k ζ U hmarked hs hg hh
  have hDn : D ≠ 0 := by intro hz; simp [hz] at hD
  obtain ⟨a,ha⟩ := PolynomialImageAvoidance.exists_eval_ne_zero
    (mul_ne_zero hDn (X_ne_zero (0 : Fin 1)))
  have hDa : eval a D ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).1
  have he : a 0 ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).2
  refine ⟨a 0,he,h (a 0) he ?_⟩
  have hconst : (fun _ : Fin 1 => a 0) = a := by ext i; fin_cases i; rfl
  rwa [hconst]

end Quartic.ActualMarkedSquareRankOmega
