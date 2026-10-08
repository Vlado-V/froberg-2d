import Froberg.HomologyCoefficientMotion
import Froberg.TargetProjection
import Mathlib.Data.ZMod.Basic

/-! Monomial parity projections and the actual endpoint Koszul complex.
The grading group is `ZMod 2`; no division by two or sign involution is used. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial Module
variable {K : Type} [Field K] {n d r : ℕ}

/-- Projection to a monomial parity, inside the ordinary homogeneous component. -/
def parityForm (w : Fin n → ZMod 2) (p : ZMod 2) : Forms K n d →ₗ[K] Forms K n d where
  toFun f := ⟨weightedHomogeneousComponent w p f.val, by
    intro a ha
    apply f.property
    intro hz
    apply ha
    simp only [coeff_weightedHomogeneousComponent,hz,ite_self]⟩
  map_add' f g := Subtype.ext ((weightedHomogeneousComponent w p).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((weightedHomogeneousComponent w p).map_smul c f.val)

@[simp] theorem parityForm_val (w : Fin n → ZMod 2) (p : ZMod 2) (f : Forms K n d) :
    (parityForm w p f).val = weightedHomogeneousComponent w p f.val := rfl

theorem parityForm_homogeneous (w : Fin n → ZMod 2) (p : ZMod 2) (f : Forms K n d) :
    (parityForm w p f).val.IsWeightedHomogeneous w p :=
  weightedHomogeneousComponent_isWeightedHomogeneous p f.val

theorem parityForm_same (w : Fin n → ZMod 2) (p : ZMod 2) (f : Forms K n d)
    (hf : f.val.IsWeightedHomogeneous w p) : parityForm w p f = f :=
  Subtype.ext hf.weightedHomogeneousComponent_same

theorem parityForm_other (w : Fin n → ZMod 2) (p q : ZMod 2) (f : Forms K n d)
    (hf : f.val.IsWeightedHomogeneous w q) (hpq : p ≠ q) : parityForm w p f = 0 :=
  Subtype.ext (hf.weightedHomogeneousComponent_ne p hpq)

theorem parityForm_decomposition (w : Fin n → ZMod 2) (p : ZMod 2) (f : Forms K n d) :
    parityForm w p f + parityForm w (p+1) f = f := by
  classical
  apply Subtype.ext
  ext a
  simp only [Submodule.coe_add,parityForm_val,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_weightedHomogeneousComponent]
  have ha : Finsupp.weight w a = p ∨ Finsupp.weight w a = p+1 := by
    generalize Finsupp.weight w a = u
    fin_cases p <;> fin_cases u <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hp : p+1 ≠ p := fun h => one_ne_zero (add_left_cancel (h.trans (add_zero p).symm))
  rcases ha with ha | ha <;> simp [ha,hp,hp.symm]

/-- Multiplying by a parity-homogeneous form shifts the monomial projection. -/
theorem parityForm_mul (w : Fin n → ZMod 2) (p e : ZMod 2)
    (q a : Forms K n d) (hq : q.val.IsWeightedHomogeneous w e) :
    parityForm w p (mulForm q a) = mulForm q (parityForm w (p-e) a) := by
  classical
  have hdec := parityForm_decomposition w (p-e) a
  have hmul : mulForm q a = mulForm q (parityForm w (p-e) a) +
      mulForm q (parityForm w (p-e+1) a) := by rw [← map_add, hdec]
  have hfirst : (mulForm q (parityForm w (p-e) a)).val.IsWeightedHomogeneous w p := by
    change (q.val * (parityForm w (p-e) a).val).IsWeightedHomogeneous w p
    have heq : e+(p-e)=p := by abel
    simpa only [heq] using hq.mul (parityForm_homogeneous w (p-e) a)
  have hsecond : (mulForm q (parityForm w (p-e+1) a)).val.IsWeightedHomogeneous w (p+1) := by
    change (q.val * (parityForm w (p-e+1) a).val).IsWeightedHomogeneous w (p+1)
    have heq : e+(p-e+1)=p+1 := by abel
    simpa only [heq] using hq.mul (parityForm_homogeneous w (p-e+1) a)
  rw [hmul,map_add,parityForm_same w p _ hfirst,
    parityForm_other w p (p+1) _ hsecond (by
      intro h
      exact one_ne_zero (add_left_cancel (h.symm.trans (add_zero p).symm))),add_zero]

/-- The source projection giving total product parity `p`. -/
def paritySource (w : Fin n → ZMod 2) (e : Fin r → ZMod 2) (p : ZMod 2) :
    (Fin r → Forms K n d) →ₗ[K] (Fin r → Forms K n d) :=
  LinearMap.pi fun i => (parityForm w (p-e i)).comp (LinearMap.proj i)

@[simp] theorem paritySource_apply (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (p : ZMod 2) (a : Fin r → Forms K n d) (i : Fin r) :
    paritySource w e p a i = parityForm w (p-e i) (a i) := rfl

theorem paritySource_decomposition (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (a : Fin r → Forms K n d) : paritySource w e 0 a + paritySource w e 1 a = a := by
  funext i
  have heq : -e i+1=1-e i := by abel
  simpa only [Pi.add_apply,paritySource_apply,zero_sub,heq] using
    parityForm_decomposition w (-e i) (a i)

theorem endpointMultiplication_paritySource (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (p : ZMod 2) (a : Fin r → Forms K n d) :
    endpointMultiplication q (paritySource w e p a) =
      parityForm w p (endpointMultiplication q a) := by
  change (∑ i, (mulForm (q i)).comp (LinearMap.proj i)) _ = _
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    paritySource_apply,endpointMultiplication,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (parityForm_mul w p (e i) (q i) (a i) (hq i)).symm

/-- Endpoint cycles decompose into actual even and odd cycles. -/
theorem paritySource_cycle (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (p : ZMod 2) (a : (endpointMultiplication q).ker) :
    paritySource w e p a.val ∈ (endpointMultiplication q).ker := by
  change endpointMultiplication q (paritySource w e p a.val) = 0
  rw [endpointMultiplication_paritySource w e q hq, a.property,map_zero]

/-- The exact space of constant boundaries involving opposite generator parities. -/
def oppositeKoszulSpace (q : Fin r → Forms K n d) (e : Fin r → ZMod 2) :
    Submodule K (Fin r → Forms K n d) :=
  Submodule.span K (koszulVector q '' {p : GeneratorPair r | e p.val.1 ≠ e p.val.2})

theorem oppositeKoszulSpace_le (q : Fin r → Forms K n d) (e : Fin r → ZMod 2) :
    oppositeKoszulSpace q e ≤ koszulSpace q := by
  apply Submodule.span_mono
  rintro _ ⟨p,_,rfl⟩
  exact ⟨p,rfl⟩

/-- Odd exactness implies every actual endpoint homology class has an even
cycle representative. The input is precisely the cross-parity exactness statement. -/
theorem exists_even_cycle_representative
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i, (a.val i).val.IsWeightedHomogeneous w (1-e i)) →
      a.val ∈ oppositeKoszulSpace q e)
    (x : EndpointHomology q) :
    ∃ a : (endpointMultiplication q).ker,
      (∀ i, (a.val i).val.IsWeightedHomogeneous w (0-e i)) ∧
      kernelClass (endpointMultiplication q) (koszulSpace q) a = x := by
  obtain ⟨a,rfl⟩ := kernelClass_surjective (endpointMultiplication q) (koszulSpace q) x
  let a0 : (endpointMultiplication q).ker :=
    ⟨paritySource w e 0 a.val,paritySource_cycle w e q hq 0 a⟩
  let a1 : (endpointMultiplication q).ker :=
    ⟨paritySource w e 1 a.val,paritySource_cycle w e q hq 1 a⟩
  have hz : kernelClass (endpointMultiplication q) (koszulSpace q) a1 = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact oppositeKoszulSpace_le q e (hodd a1 (fun i => parityForm_homogeneous w (1-e i) (a.val i)))
  refine ⟨a0,fun i => parityForm_homogeneous w (0-e i) (a.val i),?_⟩
  have ha : a0+a1=a := Subtype.ext (paritySource_decomposition w e a.val)
  have h := congrArg (kernelClass (endpointMultiplication q) (koszulSpace q)) ha
  simpa only [map_add,hz,add_zero] using h

section Projected
variable {Z : Type*} [AddCommGroup Z] [Module K Z]

/-- If the discarded target is even, every odd projected cycle is a genuine cycle. -/
theorem odd_paritySource_projected_cycle
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z, pi z=0 → parityForm w 1 z=0)
    (a : (projectedEndpointMultiplication pi q).ker) :
    paritySource w e 1 a.val ∈ (endpointMultiplication q).ker := by
  change endpointMultiplication q (paritySource w e 1 a.val)=0
  rw [endpointMultiplication_paritySource w e q hq]
  exact hpi _ a.property

/-- With an even discarded target, odd exactness supplies even representatives
for the actual projected endpoint homology as well. -/
theorem exists_even_projected_cycle_representative
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i, (q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z, pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i, (a.val i).val.IsWeightedHomogeneous w (1-e i)) →
      a.val ∈ oppositeKoszulSpace q e)
    (x : ProjectedEndpointHomology pi q) :
    ∃ a : (projectedEndpointMultiplication pi q).ker,
      (∀ i, (a.val i).val.IsWeightedHomogeneous w (0-e i)) ∧
      kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q) a = x := by
  obtain ⟨a,rfl⟩ := kernelClass_surjective (projectedEndpointMultiplication pi q) (koszulSpace q) x
  let b : (endpointMultiplication q).ker := ⟨paritySource w e 1 a.val,
    odd_paritySource_projected_cycle w e q hq pi hpi a⟩
  have hb : paritySource w e 1 a.val ∈ koszulSpace q :=
    oppositeKoszulSpace_le q e (hodd b (fun i => parityForm_homogeneous w (1-e i) (a.val i)))
  let a1 : (projectedEndpointMultiplication pi q).ker :=
    ⟨paritySource w e 1 a.val,koszulSpace_le_projected_ker pi q hb⟩
  have heven : paritySource w e 0 a.val=a.val-a1.val := by
    have heq := paritySource_decomposition w e a.val
    exact eq_sub_iff_add_eq.mpr heq
  have ha0 : paritySource w e 0 a.val ∈ (projectedEndpointMultiplication pi q).ker := by
    rw [heven]
    exact (projectedEndpointMultiplication pi q).ker.sub_mem a.property a1.property
  let a0 : (projectedEndpointMultiplication pi q).ker := ⟨paritySource w e 0 a.val,ha0⟩
  have hz : kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q) a1=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hb
  refine ⟨a0,fun i => parityForm_homogeneous w (0-e i) (a.val i),?_⟩
  have ha : a0+a1=a := Subtype.ext (paritySource_decomposition w e a.val)
  have h := congrArg (kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q)) ha
  simpa only [map_add,hz,add_zero] using h

end Projected
end Froberg
