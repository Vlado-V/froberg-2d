/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.ExtendedCorrectionRealization
public import Quartic.ExtendedDeformationResponse
public import Quartic.ActualDeformationRankOmega

/-! The full extended response is realized by persistent columns of the
actual quartic deformation whenever the marked child square is killed. -/

@[expose] public section

noncomputable section
namespace Quartic.ExtendedDeformationRank
open Module MvPolynomial ActualDeformationColumnsOmega ExtendedCorrectionRealization

variable {K : Type*} [Field K] {m c q : ℕ}

private theorem projection_annihilates
    (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    (projectionRawJ g h).comp (quadraticMultiplication (SplitBlock22.fullGenerators g h)) = 0 := by
  apply LinearMap.ext
  intro a
  change (GeneralF13.combined g h).range.mkQ
    (ActualSplitCokernel.projection13 (quadraticMultiplication (SplitBlock22.fullGenerators g h) a)) = 0
  rw [ActualSplitCokernel.projection13_multiplication]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

theorem response_realized (ω : K) (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2)
    (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (a : (quadraticMultiplication h).ker) (ha : a.val k = h k)
    (ξ : ExtendedDeformationResponse.Source ω g h r U) :
    ∃ w : Forms K (3 + m) 4,
      w ∈ PersistentColumnRank.persistent
        (quadraticMultiplication (SplitBlock22.fullGenerators g h))
        (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω)))) ∧
      projectionRawJ g h w = ExtendedDeformationResponse.response ω g h r U p ξ := by
  let R := responseSpace ω g h p r k
  have htrace : ExtendedDeformationResponse.traceResponse g h r ξ.1 ∈ R := by
    obtain ⟨b, hb, _, hr⟩ := trace_class_realized g h p r
      (Pi.single k (markedDirection ω)) ξ.1
    exact ⟨_, PersistentColumnRank.first_response_mem _ _ b hb, hr⟩
  have hcorr : ExtendedDeformationResponse.correctionResponse ω g h r U p ξ.2 ∈ R := by
    refine Submodule.Quotient.induction_on _ ξ.2 ?_
    intro z
    simpa only [ExtendedDeformationResponse.correctionResponse_mk, rawResponse_apply] using
      extended_mem ω g h p r k U hmarked hs a ha z
  have hsum := R.add_mem htrace hcorr
  exact hsum

theorem rank_principal_open (ω : K) (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2)
    (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (a : (quadraticMultiplication h).ker) (ha : a.val k = h k) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
          finrank K (ExtendedDeformationResponse.response ω g h r U p).range ≤
            finrank K (quadraticMultiplication
              (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range := by
  obtain ⟨D, hD, h⟩ := PersistentColumnRank.rank_gain_of_realizations_principal_open
    (quadraticMultiplication (SplitBlock22.fullGenerators g h))
    (quadraticMultiplication (motionFamily p r (Pi.single k (markedDirection ω))))
    (projectionRawJ g h) (ExtendedDeformationResponse.response ω g h r U p)
    (projection_annihilates g h)
    (response_realized ω g h p r k U hmarked hs a ha)
  exact ⟨D, hD, fun ε he hDε => by rw [deformed_multiplication]; exact h ε he hDε⟩

theorem independent_rank_principal_open (ω : K) (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2)
    (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (a : (quadraticMultiplication h).ker) (ha : a.val k = h k)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        LinearIndependent K (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε) ∧
        finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
          finrank K (ExtendedDeformationResponse.response ω g h r U p).range ≤
            finrank K (quadraticMultiplication
              (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range := by
  obtain ⟨D, hD, hRank⟩ := rank_principal_open ω g h p r k U hmarked hs a ha
  obtain ⟨E, hE, he⟩ := DeformationIndependence.principal_open g h p r
    (Pi.single k (markedDirection ω)) hg hh
  refine ⟨D * E, by simpa only [map_mul] using mul_ne_zero hD hE, ?_⟩
  intro ε hε hDE
  have hne : eval (fun _ => ε) D ≠ 0 ∧ eval (fun _ => ε) E ≠ 0 := by
    apply mul_ne_zero_iff.mp
    simpa only [map_mul] using hDE
  exact ⟨he ε hne.2, hRank ε hε hne.1⟩

theorem exists_independent_rank_gain [Infinite K]
    (ω : K) (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2)
    (r : Fin 4 → Forms K m 2) (k : Fin q)
    (U : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k U)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (a : (quadraticMultiplication h).ker) (ha : a.val k = h k)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ ε : K, ε ≠ 0 ∧
      LinearIndependent K (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε) ∧
      finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range +
        finrank K (ExtendedDeformationResponse.response ω g h r U p).range ≤
          finrank K (quadraticMultiplication
            (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range := by
  obtain ⟨D, hD, h⟩ := independent_rank_principal_open ω g h p r k U hmarked hs a ha hg hh
  have hDn : D ≠ 0 := by intro hz; simp [hz] at hD
  obtain ⟨x, hx⟩ := PolynomialImageAvoidance.exists_eval_ne_zero
    (mul_ne_zero hDn (X_ne_zero (0 : Fin 1)))
  have hDx : eval x D ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hx)).1
  have he : x 0 ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hx)).2
  refine ⟨x 0, he, h (x 0) he ?_⟩
  have hconst : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
  rwa [hconst]

end Quartic.ExtendedDeformationRank
