import Froberg.PreparedOuterSeparationOpen
import Froberg.SharedFrameQuadraticWitness

/-! A shared quadratic detector and the separated scalar coefficient space
supply the actual private/outer witness required by the full parameter open. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PreparedParameters PreparedTarget FullPreparedParameters PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {h a z d q r f u c : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem prepared_outer_open_of_detected_scalar_witness
    {I : Type*} [Fintype I] [DecidableEq I]
    (hd : 3≤d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hmin : ∀ j∈J,2≤j) (idx : Fin r ≃ PreparedParameters.Label q J counts)
    (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
    (L : Forms K h 2 →ₗ[K] (Fin c → K))
    (hO₂ : O 2≤(quadraticPolynomialDetector L).ker)
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
    letI : Module.Finite K (FixedPureZeroScalarSpace (a+z) d q f u J counts O) :=
      finite_fixedPureZeroScalarSpace hO
    ∃ D : MvPolynomial (Fin (finrank K (FixedPureZeroScalarSpace (a+z) d q f u J counts O))) K,
      (∃ p : FixedPureZeroScalarSpace (a+z) d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ (U : Fin u → Forms K h d) (p : FixedPureZeroScalarSpace (a+z) d q f u J counts O),
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          PreparedOuterSeparation (by omega) ho hO hJ heven U p := by
  letI : Module.Finite K (FixedPureZeroScalarSpace (a+z) d q f u J counts O) :=
    finite_fixedPureZeroScalarSpace hO
  let P := privatePowerBiform (a := a) (d := d) (fun i => e (w i)) ι
  obtain ⟨F,_,hexact,hsep⟩ := exists_shared_frame_quadratic_witness
    hd e L w ι hker Q hQ o hdet C hCdeg hC hCQ hf
  exact prepared_outer_separation_principal_open_uniform hd ho hO hJ heven hmin idx
    (quadraticPolynomialDetector L) (quadraticPolynomialDetector_supported L) hO₂
    (fun i => renameForm (Fin.castAdd z) (Q i)) P F hexact hsep

end Froberg
