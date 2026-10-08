import Froberg.OddBottomDetection
import Froberg.OddBackgroundEndpoint

/-! The zero-bottom exclusion on the literal Q/F/G background quotient. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

theorem coreWeight_eq_blockWeight :
    coreWeight h m=blockWeight h m ∘ finSumFinEquiv.symm := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [coreWeight,blockWeight]

theorem coreParity_eq_blockParity :
    coreParity h m=(fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm := by
  funext i
  exact congrArg (fun n : ℕ => (n : ZMod 2)) (congrFun coreWeight_eq_blockWeight i)

theorem oddBackgroundEndpointEquiv_mk (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (a : biformParitySpace K h m (2*d) 1) :
    oddBackgroundEndpointEquiv Q F G ((fullOddRelations Q F G).mkQ a)=
      oddTargetClass ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
        (backgroundEnumeratedForms Q F G)
        (parityPolynomialToFormsEquiv finSumFinEquiv
          (fun i => (blockWeight h m i : ZMod 2)) 1 a).val := by
  apply Subtype.ext
  let p := parityPolynomialToFormsEquiv finSumFinEquiv
    (fun i => (blockWeight h m i : ZMod 2)) 1 a
  change (projectedEndpointMultiplication (LinearMap.id : Forms K (h+m) (2*d) →ₗ[K] _)
    (backgroundEnumeratedForms Q F G)).range.mkQ p.val=
    (projectedEndpointMultiplication (LinearMap.id : Forms K (h+m) (2*d) →ₗ[K] _)
    (backgroundEnumeratedForms Q F G)).range.mkQ (parityForm _ 1 p.val)
  rw [parityForm_same _ 1 p.val p.property]

theorem oddBackground_bottom_detects (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (hupper : Function.Surjective (upperTargetMap (backgroundEnumeratedForms Q F G)))
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) →ₗ[K] K)
    (hbottom : ∀ a : biformParitySpace K h m (2*d) 1,
      a.val.IsWeightedHomogeneous (blockWeight h m) 1 →
        ell ((fullOddRelations Q F G).mkQ a)=0) : ell=0 := by
  let w := (fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm
  let E := oddBackgroundEndpointEquiv Q F G
  have hw : coreParity h m=w := coreParity_eq_blockParity
  have hpar : ∀ i,(backgroundEnumeratedForms Q F G i).val.IsWeightedHomogeneous w
      ((backgroundParity ∘ (Fintype.equivFin (BackgroundLabel q f u)).symm) i) :=
    parityEnumeratedForms_homogeneous _ _ _ _ _
  have hlow : ∀ p : Forms K (h+m) (2*d),
      p.val.IsWeightedHomogeneous (coreWeight h m) 1 →
        (ell.comp E.symm.toLinearMap) (oddTargetClass w (backgroundEnumeratedForms Q F G) p)=0 := by
    intro p hp
    have hpw : p.val.IsWeightedHomogeneous w 1 := by
      rw [←hw]
      exact weighted_homogeneous_has_parity (coreWeight h m) p.val hp
    let pp : parityPartForms (K := K) (d := 2*d) w 1 := ⟨p,hpw⟩
    let a := (parityPolynomialToFormsEquiv finSumFinEquiv
      (fun i => (blockWeight h m i : ZMod 2)) 1).symm pp
    have ha : a.val.IsWeightedHomogeneous (blockWeight h m) 1 := by
      change (rename finSumFinEquiv.symm p.val).IsWeightedHomogeneous (blockWeight h m) 1
      apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding (blockWeight h m) p.val 1
      change p.val.IsWeightedHomogeneous (blockWeight h m ∘ finSumFinEquiv.symm) 1
      rw [←coreWeight_eq_blockWeight]
      exact hp
    have he : E ((fullOddRelations Q F G).mkQ a)=
        oddTargetClass w (backgroundEnumeratedForms Q F G) p := by
      simpa only [a,LinearEquiv.apply_symm_apply,pp] using
        oddBackgroundEndpointEquiv_mk Q F G a
    change ell (E.symm (oddTargetClass w (backgroundEnumeratedForms Q F G) p))=0
    rw [←he,E.symm_apply_apply]
    exact hbottom a ha
  have hzero : ell.comp E.symm.toLinearMap=0 := by
    have ht := oddTarget_bottom_detects
      (backgroundParity ∘ (Fintype.equivFin (BackgroundLabel q f u)).symm)
      (backgroundEnumeratedForms Q F G)
    rw [hw] at ht
    exact ht hpar hupper (ell.comp E.symm.toLinearMap) hlow
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hzero (E x)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,E.symm_apply_apply,
    LinearMap.zero_apply] using hx

end Froberg
