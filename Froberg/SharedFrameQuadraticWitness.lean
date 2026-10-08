import Froberg.TypedPrivateQuadraticExistence
import Froberg.PrivateBiformFamily
import Froberg.PrivateFrameDetector

/-! The linear coordinates returned by the common-frame construction give
the typed private-power witness with no additional choice of detector. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K] {h a z d r f u c : ℕ}

theorem quadraticPolynomialDetector_supported
    (L : Forms K h 2 →ₗ[K] (Fin c → K)) :
    (quadraticPolynomialDetector L).comp (homogeneousComponent 2)=quadraticPolynomialDetector L := by
  apply LinearMap.ext
  intro p
  change L ⟨homogeneousComponent 2 (homogeneousComponent 2 p),_⟩=
    L ⟨homogeneousComponent 2 p,_⟩
  congr 1
  exact Subtype.ext (homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous 2 p))

theorem exists_shared_frame_quadratic_witness {I : Type*} [Fintype I] [DecidableEq I]
    (hd : 3≤d) (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (w : Fin u → Fin h → K) (ι : Fin u ↪ Fin z)
    (hker : (privatePolynomialMap (a := a) (s := d-1) ι
      (fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
        Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := d-1) ι w))))
    (Q : Fin r → Forms K a d) (hQ : ∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t))
    (o : I → Forms K h 1)
    (hdet : LinearIndependent K (fun p => quadraticPolynomialDetector L
      (pairProducts (fun i => (o i).val) p)))
    (C : Submodule K (Poly K a)) (hCdeg : C≤Forms K a (d-1))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCQ : Disjoint (C*C) (familySpace Q*Forms K a (d-2)))
    (hf : f≤Fintype.card I*(finrank K C/2)) :
    ∃ F : Fin f → FullBiform K (Fin h) (a+z) 1 (d-1), LinearIndependent K F ∧
      (quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) (a+z) 1 (d-1)).subtype
        (biformVectorDetector (quadraticPolynomialDetector L))
        (fun i => renameForm (Fin.castAdd z) (Q i))
        (privatePowerBiform (a := a) (d := d) (fun i => e (w i)) ι)).ker=
      (quadraticNuisanceBoundary (privatePowerBiform (a := a) (d := d) (fun i => e (w i)) ι)).range ∧
      ∀ x v,quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) (a+z) 1 (d-1)).subtype
        (biformVectorDetector (quadraticPolynomialDetector L))
        (fun i => renameForm (Fin.castAdd z) (Q i))
        (privatePowerBiform (a := a) (d := d) (fun i => e (w i)) ι) x+
        detectedSymmetricProductRow (FullBiform K (Fin h) (a+z) 1 (d-1)).subtype
          (biformVectorDetector (quadraticPolynomialDetector L)) F v=0 → v=0 := by
  let bo : Basis (Fin h) K (Forms K h 1) := (Pi.basisFun K (Fin h)).map e
  have hb (j : Fin h) : bo j=e (Pi.single j 1) := by
    simp only [bo,Basis.map_apply,Pi.basisFun_apply]
  let A := fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap
  have hA (i : Fin u) (j : Fin h) :
      quadraticPolynomialDetector L (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=
        A i (Pi.single j 1) := by
    simp only [hb]
    exact quadraticPolynomialDetector_private_column e L (w i) j
  let P := privatePowerBiform (a := a) (d := d) (fun i => e (w i)) ι
  have hP (i : Fin u) : (P i).val=
      rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)) := by
    simp only [P,privatePowerBiform_val,hb,outputCombination_equiv_basis]
  exact exists_typed_private_quadratic_witness
    hd bo (quadraticPolynomialDetector L) w ι A hA hker P hP Q hQ o hdet C hCdeg hC hCQ hf

end Froberg
