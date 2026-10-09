module

public import Froberg.ParityPolynomialEndpoint
public import Froberg.OddBackgroundQuotient

@[expose] public section

/-! The background odd quotient is the odd part of the actual endpoint
quotient. Both the variable and generator enumerations are explicit. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

abbrev BackgroundLabel (q f u : ℕ) := Fin q ⊕ (Fin f ⊕ Fin u)

def backgroundParity : BackgroundLabel q f u → ZMod 2 :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 1))

def backgroundParityFamily (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (i : BackgroundLabel q f u) → homogeneousParitySpace K (Fin h ⊕ Fin m) d
      (fun i => (blockWeight h m i : ZMod 2)) (backgroundParity i)
  | Sum.inl i => Q i
  | Sum.inr (Sum.inl i) => F i
  | Sum.inr (Sum.inr i) => G i

def backgroundParityCoefficients :
    ((Fin q → biformParitySpace K h m d 1) ×
      (Fin f → biformParitySpace K h m d 0) × (Fin u → biformParitySpace K h m d 0)) →ₗ[K]
      ((i : BackgroundLabel q f u) → homogeneousParitySpace K (Fin h ⊕ Fin m) d
        (fun i => (blockWeight h m i : ZMod 2)) (1-backgroundParity i)) where
  toFun a
    | Sum.inl i => by simpa [backgroundParity,biformParitySpace,homogeneousParitySpace] using a.1 i
    | Sum.inr (Sum.inl i) => by simpa [backgroundParity,biformParitySpace,homogeneousParitySpace] using a.2.1 i
    | Sum.inr (Sum.inr i) => by simpa [backgroundParity,biformParitySpace,homogeneousParitySpace] using a.2.2 i
  map_add' a b := by funext i;rcases i with i | (i | i) <;> rfl
  map_smul' c a := by funext i;rcases i with i | (i | i) <;> rfl

theorem backgroundParityCoefficients_surjective :
    Function.Surjective (backgroundParityCoefficients (K := K) (h := h) (m := m)
      (d := d) (q := q) (f := f) (u := u)) := by
  intro a
  let x : Fin q → biformParitySpace K h m d 1 := fun i => by
    simpa [backgroundParity,biformParitySpace,homogeneousParitySpace] using a (Sum.inl i)
  let y : Fin f → biformParitySpace K h m d 0 := fun i => by
    simpa [backgroundParity,biformParitySpace,homogeneousParitySpace] using a (Sum.inr (Sum.inl i))
  let z : Fin u → biformParitySpace K h m d 0 := fun i => by
    simpa [backgroundParity,biformParitySpace,homogeneousParitySpace] using a (Sum.inr (Sum.inr i))
  refine ⟨(x,y,z),?_⟩
  funext i
  rcases i with i | (i | i) <;> rfl

theorem backgroundParityEndpoint_comp (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (parityPolynomialEndpoint (fun i => (blockWeight h m i : ZMod 2)) backgroundParity
      (backgroundParityFamily Q F G) 1).comp backgroundParityCoefficients=
      (evenScalarOddFamily Q).coprod
        ((privateEvenCoefficientMap F).coprod (privateEvenCoefficientMap G)) := by
  apply LinearMap.ext
  intro a
  change parityPolynomialEndpoint _ _ _ _ (backgroundParityCoefficients a)=
    evenScalarOddFamily Q a.1 + (privateEvenCoefficientMap F a.2.1 + privateEvenCoefficientMap G a.2.2)
  apply Subtype.ext
  simp [parityPolynomialEndpoint_val,backgroundParityFamily,backgroundParityCoefficients,
    evenScalarOddFamily,evenScalarOddProduct,privateEvenCoefficientMap_val,
    Submodule.coe_add,
    Fintype.sum_sum_type]

theorem fullOddRelations_eq_parityEndpoint_range (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    fullOddRelations Q F G=
      (parityPolynomialEndpoint (fun i => (blockWeight h m i : ZMod 2)) backgroundParity
        (backgroundParityFamily Q F G) 1).range := by
  have hr := congrArg LinearMap.range (backgroundParityEndpoint_comp Q F G)
  rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr backgroundParityCoefficients_surjective,
    Submodule.map_top,LinearMap.range_coprod,LinearMap.range_coprod] at hr
  exact (show _ = _ from (by simpa [fullOddRelations,oddBackgroundRelations,sup_assoc] using hr)).symm

def backgroundEnumeratedForms (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    Fin (Fintype.card (BackgroundLabel q f u)) → Forms K (h+m) d :=
  parityEnumeratedForms finSumFinEquiv (Fintype.equivFin _) _ backgroundParity
    (backgroundParityFamily Q F G)

/-- This is the literal endpoint quotient, with no dimension or exactness
assumption on the background generators. -/
def oddBackgroundEndpointEquiv (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) ≃ₗ[K]
      oddTargetSpace ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
        (backgroundEnumeratedForms Q F G) :=
  (Submodule.quotEquivOfEq _ _ (fullOddRelations_eq_parityEndpoint_range Q F G)).trans
    (parityPolynomialEndpointQuotientEquiv finSumFinEquiv (Fintype.equivFin _) _
      backgroundParity (backgroundParityFamily Q F G))

end Froberg
