import Froberg.PreparedQuadraticDenominator
import Froberg.QuadraticRowFormalSeparation
import Froberg.HomogeneousRename
import Froberg.QuadraticQuotientSeparation

/-! The actual low-component coefficient row supplies C.2 for the displayed
homogeneous outer family and background, uniformly in every later supported
scalar deletion. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d c q b f : ℕ}

theorem prepared_quadratic_formal_separation
    (hd : 2≤d) (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T)
    (Q : Fin q → Forms K m d)
    (P : Fin b → FullBiform K (Fin h) m 1 (d-1))
    (F : Fin f → FullBiform K (Fin h) m 1 (d-1))
    (qF : Fin f → Forms K (h+m) d)
    (hqF : ∀ i,(qF i).val=rename finSumFinEquiv (F i).val)
    (D₂ : Submodule K (Poly K h)) (hD₂ : D₂≤T.ker)
    (W : Submodule K (Forms K (h+m) d))
    (H : PreparedLowComponents W (polynomialTensorSpace (Forms K h 0) (familySpace Q))
      (Submodule.span K (Set.range (fun i => rename finSumFinEquiv (P i).val)))
      (polynomialTensorSpace D₂ (Forms K m (d-2))))
    (hrow : ∀ x a,
      quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) Q P x+
      detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) F a=0 → a=0)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d)
      (Fin.natAdd h : Fin m → Fin (h+m))).range) :
    formalSquare (Submodule.span K (Set.range qF)) ⊓
      ((formalMixed W).map (D.mkQ.comp formalPolynomialMultiplication)).comap
        (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥ := by
  let A := quadraticNuisanceRow (t := d-2) (FullBiform K (Fin h) m 1 (d-1)).subtype
    (biformVectorDetector T) Q P
  let R := (preparedQuadraticDetector T).comp (Forms K (h+m) (2*d)).subtype
  apply formalSquare_separated_of_coefficient_row formalPolynomialMultiplication R A qF W
  · intro x a ha
    apply hrow x a
    have hp (s : Sym2 (Fin f)) :
        R (formalPolynomialMultiplication (formalPair qF s))=
          biformVectorDetector T (pairProducts (fun i => (F i).val) s) := by
      induction s using Sym2.inductionOn with
      | _ i j =>
        change preparedQuadraticDetector T
          (formalPolynomialMultiplication (formalPair qF s(i,j))).val=_
        rw [formalPair_mk,formalPolynomialMultiplication_symProd]
        change preparedQuadraticDetector T ((qF i).val*(qF j).val)=_
        rw [hqF,hqF,←map_mul,preparedQuadraticDetector_rename,pairProducts_mk]
    simpa only [hp,detectedSymmetricProductRow,LinearMap.coe_mk,AddHom.coe_mk,Submodule.subtype_apply,A] using ha
  · have hker := formalMixed_polynomial_map_le_ker W
      (A.range.mkQ.comp (preparedQuadraticDetector T)) (by
        intro w hw a
        exact (Submodule.Quotient.mk_eq_zero A.range).mpr
          (prepared_background_mem_quadratic_row hd T hT Q P D₂ hD₂ W H w hw a))
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero A.range).mp (hker hy)
  · intro y hy
    obtain ⟨a,ha⟩ := hD hy
    rw [←ha]
    change preparedQuadraticDetector T (rename (Fin.natAdd h) a.val)∈A.range
    rw [preparedQuadraticDetector_scalar T hT]
    exact Submodule.zero_mem _

end Froberg
