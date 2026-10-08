import Froberg.SecondStageParameters
import Froberg.PolynomialLinearAvoidance

/-! Two-stage incidence in the actual finite-dimensional equation spaces.
The first vector is universally quantified; only the final parameter is chosen. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Matrix Quartic Quartic.KernelPolynomialCharts
variable {K X Y U V : Type*} [Field K] [Infinite K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {q N s fcount r₁ r₂ : ℕ}

theorem intrinsic_second_stage_with_parameters
    {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (degrees : Fin fcount → ℕ) (f : ∀ i,Forms K q (degrees i))
    (ell : Fin (s+1) → Forms K q 1)
    (hempty : ∀ t : Fin q → L,(∀ i,aeval t (f i).val=0) →
      (∀ j,aeval t (ell j).val=0) → t=0)
    (A : (Fin (q+N) → K) → X →ₗ[K] U)
    (B : (Fin (q+N) → K) → X → Y →ₗ[K] V)
    (hA : IsPolynomialFamily A)
    (hB : IsPolynomialFamily (fun p : (Fin (q+N) ⊕ Fin (finrank K X)) → K =>
      B (fun i => p (.inl i)) ((Module.finBasis K X).equivFun.symm (fun i => p (.inr i)))))
    (hcount : s+N+finrank K X<r₁+r₂) :
    ∃ P : MvPolynomial (Fin (finrank K Y)) K,
      (∃ z,eval z P≠0) ∧ ∀ z,eval z P≠0 →
        ∀ (x : X) (t : Fin q → K),
          (∀ i,eval t (f i).val=0) → eval t (ell 0).val=1 → ∀ u : Fin N → K,
          r₁≤finrank K (A (Fin.append t u)).range →
          r₂≤finrank K (B (Fin.append t u) x).range →
          A (Fin.append t u) x≠0 ∨
            B (Fin.append t u) x ((Module.finBasis K Y).equivFun.symm z)≠0 := by
  classical
  let bx := Module.finBasis K X
  let bY := Module.finBasis K Y
  let bu := Module.finBasis K U
  let bv := Module.finBasis K V
  have ha (i : Fin (finrank K U)) (j : Fin (finrank K X)) :
      ∃ p : MvPolynomial (Fin (q+N)) K,∀ t,eval t p=bu.repr (A t (bx j)) i :=
    hA ((bu.coord i).comp (LinearMap.applyₗ (R := K) (M₂ := U) (bx j)))
  have hb (i : Fin (finrank K V)) (j : Fin (finrank K Y)) :
      ∃ p : MvPolynomial (Fin (q+N) ⊕ Fin (finrank K X)) K,∀ t,
        eval t p=bv.repr (B (fun k => t (.inl k)) (bx.equivFun.symm (fun k => t (.inr k))) (bY j)) i :=
    hB ((bv.coord i).comp (LinearMap.applyₗ (R := K) (M₂ := V) (bY j)))
  choose MA hMA using ha
  choose MB hMB using hb
  have hea (t : Fin (q+N) → K) : evaluated MA t=LinearMap.toMatrix bx bu (A t) := by
    ext i j
    simpa only [evaluated,Matrix.map_apply,LinearMap.toMatrix_apply] using hMA i j t
  have heb (t : Fin (q+N) → K) (x : X) :
      evaluated MB (Sum.elim t (bx.equivFun x))=LinearMap.toMatrix bY bv (B t x) := by
    ext i j
    simpa only [evaluated,Matrix.map_apply,LinearMap.toMatrix_apply,Sum.elim_inl,Sum.elim_inr,LinearEquiv.symm_apply_apply] using
      hMB i j (Sum.elim t (bx.equivFun x))
  obtain ⟨P,hP,hgood⟩ := principal_open_second_dehom_with_parameters degrees f ell hempty MA MB hcount
  refine ⟨P,hP,?_⟩
  intro z hz x t hf hell u hr hs
  have hr' : r₁≤(evaluated MA (Fin.append t u)).rank := by
    rw [hea,Matrix.rank_eq_finrank_range_toLin _ bu bx,Matrix.toLin_toMatrix]
    exact hr
  have hs' : r₂≤(evaluated MB (Sum.elim (Fin.append t u) (bx.equivFun x))).rank := by
    rw [heb,Matrix.rank_eq_finrank_range_toLin _ bv bY,Matrix.toLin_toMatrix]
    exact hs
  have hh := hgood z hz (bx.equivFun x) t hf hell u hr' hs'
  contrapose! hh
  constructor
  · rw [hea]
    have he := (A (Fin.append t u)).toMatrix_mulVec_repr bx bu x
    change Matrix.mulVec (LinearMap.toMatrix bx bu (A (Fin.append t u)))
      (bx.equivFun x)=bu.equivFun (A (Fin.append t u) x) at he
    rw [hh.1,map_zero] at he
    exact he
  · rw [heb]
    have he := (B (Fin.append t u) x).toMatrix_mulVec_repr bY bv (bY.equivFun.symm z)
    change Matrix.mulVec (LinearMap.toMatrix bY bv (B (Fin.append t u) x))
      (bY.equivFun (bY.equivFun.symm z))=bv.equivFun
        (B (Fin.append t u) x (bY.equivFun.symm z)) at he
    rw [LinearEquiv.apply_symm_apply,hh.2,map_zero] at he
    exact he

end Froberg
