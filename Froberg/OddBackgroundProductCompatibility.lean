import Froberg.OddBackgroundProduct
import Froberg.OddBackgroundBottomDetection

/-! The concrete polynomial quotient multiplication is the actual endpoint
odd multiplication under the source and target quotient equivalences. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

@[simp] theorem oddBackgroundSourceEquiv_mk_val
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (a : biformParitySpace K h m d 1) :
    (oddBackgroundSourceEquiv Q F G ((oddBackgroundCoefficientRelations F G).mkQ a)).val=
      (Submodule.span K (Set.range (backgroundEnumeratedForms Q F G))).mkQ
        (parityPolynomialToFormsEquiv finSumFinEquiv
          (fun i => (blockWeight h m i : ZMod 2)) 1 a).val := rfl

def evenPolynomialToForms : biformParitySpace K h m d 0 →ₗ[K] Forms K (h+m) d :=
  (parityPartForms ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm) 0).subtype.comp
    (parityPolynomialToFormsEquiv finSumFinEquiv
      (fun i => (blockWeight h m i : ZMod 2)) 0).toLinearMap

@[simp] theorem evenPolynomialToForms_val (a : biformParitySpace K h m d 0) :
    (evenPolynomialToForms a).val=rename finSumFinEquiv a.val := rfl

theorem evenPolynomialToForms_parity (a : biformParitySpace K h m d 0) :
    (evenPolynomialToForms a).val.IsWeightedHomogeneous
      ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm) 0 :=
  (parityPolynomialToFormsEquiv finSumFinEquiv
    (fun i => (blockWeight h m i : ZMod 2)) 0 a).property

theorem oddBackgroundQuotientProduct_compatible
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (p : biformParitySpace K h m d 0)
    (a : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddBackgroundEndpointEquiv Q F G (oddBackgroundQuotientProduct Q F G p a)=
      oddQuotientProduct ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
        (backgroundEnumeratedForms Q F G) evenPolynomialToForms evenPolynomialToForms_parity
        p (oddBackgroundSourceEquiv Q F G a) := by
  obtain ⟨v,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective a
  rw [oddBackgroundQuotientProduct_mk,oddBackgroundEndpointEquiv_mk]
  apply Subtype.ext
  rw [oddQuotientProduct_val,oddBackgroundSourceEquiv_mk_val]
  let z := parityPolynomialToFormsEquiv finSumFinEquiv
    (fun i => (blockWeight h m i : ZMod 2)) 1 (evenOddBiformProduct p v)
  change (projectedEndpointMultiplication (LinearMap.id : Forms K (h+m) (2*d) →ₗ[K] _)
    (backgroundEnumeratedForms Q F G)).range.mkQ (parityForm _ 1 z.val)=_
  rw [parityForm_same _ 1 z.val z.property]
  change _=(projectedEndpointMultiplication (LinearMap.id : Forms K (h+m) (2*d) →ₗ[K] _)
    (backgroundEnumeratedForms Q F G)).range.mkQ
      (mulForm (evenPolynomialToForms p)
        (parityPolynomialToFormsEquiv finSumFinEquiv
          (fun i => (blockWeight h m i : ZMod 2)) 1 v).val)
  congr 1
  apply Subtype.ext
  change rename finSumFinEquiv (p.val*v.val)=
    rename finSumFinEquiv p.val*rename finSumFinEquiv v.val
  exact map_mul _ _ _

end Froberg
