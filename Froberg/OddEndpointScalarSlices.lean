import Froberg.OddEvenBottomDetection
import Froberg.ClosedKernelEquivalence
import Froberg.ScalarQuotientSlices

/-! Closed scalar-multiplication slices on the relative quotient are
slices of the actual enlarged endpoint odd multiplication. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial
open BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

def scalarEndpointEmbedding : Forms K m d →ₗ[K] Forms K (h+m) d :=
  evenPolynomialToForms.comp scalarEvenBiform

theorem scalarEndpointEmbedding_parity (p : Forms K m d) :
    (scalarEndpointEmbedding (h := h) p).val.IsWeightedHomogeneous
      ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm) 0 :=
  evenPolynomialToForms_parity (scalarEvenBiform p)


def oddEndpointScalarAction
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :=
  (oddQuotientProduct ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
    (backgroundEnumeratedForms Q F G) evenPolynomialToForms evenPolynomialToForms_parity).comp
      (scalarEvenBiform (K := K) (h := h) (m := m) (d := d))

theorem oddEndpointScalarAction_eq
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    oddEndpointScalarAction Q F G=
      oddQuotientProduct ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
        (backgroundEnumeratedForms Q F G) scalarEndpointEmbedding scalarEndpointEmbedding_parity := by
  rfl


theorem oddEvenEndpointScalar_compatible
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (p : Forms K m d)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddEvenEndpointExtensionEquiv Q F G E
      ((oddEvenRelativeMap Q F G E).range.mkQ (oddBackgroundScalarProduct Q F G p v))=
      oddEndpointScalarAction (Fin.append Q E) F G p
        (oddBackgroundSourceEquiv (Fin.append Q E) F G v) := by
  obtain ⟨a,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective v
  change oddBackgroundEndpointEquiv (Fin.append Q E) F G
    (oddEvenTargetExtensionEquiv Q F G E ((oddEvenRelativeMap Q F G E).range.mkQ
      ((fullOddRelations Q F G).mkQ (evenOddBiformProduct (scalarEvenBiform p) a))))=_
  rw [oddEvenTargetExtensionEquiv_mk]
  exact oddBackgroundQuotientProduct_compatible (Fin.append Q E) F G (scalarEvenBiform p)
    ((oddBackgroundCoefficientRelations F G).mkQ a)

theorem oddEndpointScalarAction_closed_slices
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) (s : ℕ → ℕ)
    (hs : HasClosedKernelSlices
      (targetPostcompose (oddBackgroundScalarProduct Q F G) (oddEvenRelativeMap Q F G E).range.mkQ) s) :
    HasClosedKernelSlices (oddEndpointScalarAction (Fin.append Q E) F G) s := by
  apply HasClosedKernelSlices.equiv (LinearEquiv.refl K (Forms K m d))
    (oddBackgroundSourceEquiv (Fin.append Q E) F G) (oddEvenEndpointExtensionEquiv Q F G E)
    _ _ _ s hs
  intro p v
  exact oddEvenEndpointScalar_compatible Q F G E p v

end Froberg
