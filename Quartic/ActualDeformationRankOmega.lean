module

public import Quartic.ActualDeformationColumnsOmega
public import Quartic.DeformationRank
public import Quartic.DeformationIndependence

@[expose] public section

/-!
# Rank gain for the actual quartic deformation

The literal quadratic deformation has independent generators and gains the
full rank of its actual trace-plus-correction response on a nonempty open
of nonzero scalar parameters. Exact source corrections supply the rank
argument; neither a source-homology inventory nor a matrix factorization is
assumed. The marked representative hypothesis holds for the canonical
actual child-cycle coefficient image.
-/
noncomputable section
namespace Quartic.ActualDeformationRankOmega
open Module MvPolynomial ActualDeformationColumnsOmega
variable {K : Type*} [Field K] [Infinite K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 2000000

/-- The retained cokernel projection kills every actual split multiplication column. -/
theorem projection_annihilates (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    (projectionRawJ g h).comp (quadraticMultiplication (SplitBlock22.fullGenerators g h)) = 0 := by
  apply LinearMap.ext
  intro a
  change (GeneralF13.combined g h).range.mkQ
    (ActualSplitCokernel.projection13 (quadraticMultiplication (SplitBlock22.fullGenerators g h) a)) = 0
  rw [ActualSplitCokernel.projection13_multiplication]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩

/-- Multiplying a trace column by the parameter puts both response summands at order two. -/
theorem response_realized (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U)
    (ξ : ActualDeformationResponseOmega.Source ω g h r U) :
    ∃ a b : Fin (4+(c+q)) → Forms K (3+m) 2,
      quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0 ∧
      quadraticMultiplication (SplitBlock22.fullGenerators g h) b =
        -quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))) a ∧
      projectionRawJ g h (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))) b) =
        ActualDeformationResponseOmega.response ω g h r U p ξ := by
  obtain ⟨a₃,h₃,_,hr₃⟩ := trace_class_realized g h p r (Pi.single k (markedDirection ω)) ξ.1
  obtain ⟨a,b,ha,hb,_,hr⟩ := correction_class_realized ω g h p r k U hmarked ξ.2
  refine ⟨a,b+a₃,ha,?_,?_⟩
  · rw [map_add,hb,h₃,add_zero]
  · rw [map_add,map_add,hr,hr₃]
    exact add_comm _ _

/-- A concrete principal open gives the actual split-rank plus response-rank bound. -/
theorem rank_principal_open (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
          finrank K (ActualDeformationResponseOmega.response ω g h r U p).range ≤
            finrank K (quadraticMultiplication
              (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range := by
  obtain ⟨D,hD,h⟩ := DeformationRank.rank_gain_of_realizations_principal_open
    (quadraticMultiplication (SplitBlock22.fullGenerators g h))
    (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))))
    (projectionRawJ g h) (ActualDeformationResponseOmega.response ω g h r U p)
    (projection_annihilates g h) (response_realized ω g h p r k U hmarked)
  exact ⟨D,hD,fun ε he hDε => by rw [deformed_multiplication]; exact h ε he hDε⟩

/-- The same concrete nonempty open enforces independence and the full actual deformation rank gain. -/
theorem independent_rank_principal_open (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U) (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        LinearIndependent K (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε) ∧
        finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
          finrank K (ActualDeformationResponseOmega.response ω g h r U p).range ≤
            finrank K (quadraticMultiplication
              (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range := by
  obtain ⟨D,hD,hRank⟩ := rank_principal_open ω g h p r k U hmarked
  obtain ⟨E,hE,he⟩ := DeformationIndependence.principal_open g h p r (Pi.single k (markedDirection ω)) hg hh
  refine ⟨D*E,by simpa only [map_mul] using mul_ne_zero hD hE,?_⟩
  intro ε hε hDE
  have hne : eval (fun _ => ε) D ≠ 0 ∧ eval (fun _ => ε) E ≠ 0 := by
    apply mul_ne_zero_iff.mp
    simpa only [map_mul] using hDE
  exact ⟨he ε hne.2,hRank ε hε hne.1⟩

/-- Some actual nonzero perturbation has independent generators and the proved full rank gain. -/
theorem exists_independent_rank_gain (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U) (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ ε : K, ε ≠ 0 ∧ LinearIndependent K (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε) ∧
      finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
        finrank K (ActualDeformationResponseOmega.response ω g h r U p).range ≤
          finrank K (quadraticMultiplication
            (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range := by
  obtain ⟨D,hD,h⟩ := independent_rank_principal_open ω g h p r k U hmarked hg hh
  have hDn : D ≠ 0 := by intro hz; simp [hz] at hD
  obtain ⟨a,ha⟩ := PolynomialImageAvoidance.exists_eval_ne_zero
    (mul_ne_zero hDn (X_ne_zero (0 : Fin 1)))
  have hDa : eval a D ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).1
  have he : a 0 ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).2
  refine ⟨a 0,he,h (a 0) he ?_⟩
  have hconst : (fun _ : Fin 1 => a 0) = a := by ext i; fin_cases i; rfl
  rwa [hconst]

end Quartic.ActualDeformationRankOmega
