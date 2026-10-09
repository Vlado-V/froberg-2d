module

public import Froberg.BiformActionPolynomial
public import Froberg.BiformOddRows
public import Froberg.EvenCoefficientElimination

@[expose] public section

/-! Actual polynomial coefficient-row consequences of the homogeneous
tensor incidence opens. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct MvPolynomial
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K]
variable {h n d b qS qO : ℕ}

/-- Injectivity of the intrinsic two-biform map eliminates every genuine
polynomial coefficient pair in this output degree. -/
theorem higher_odd_polynomial_row (hb : 1≤b) (hbd : b≤d)
    (p : (Fin qS → Forms K h 0 ⊗[K] Forms K n d) ×
      (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)))
    (hp : Function.Injective (twoFamilyMultiplication (K := K)
      (P₁ := Forms K h 0 ⊗[K] Forms K n d)
      (P₂ := Forms K h 1 ⊗[K] Forms K n (d-1))
      (V₁ := Forms K h b ⊗[K] Forms K n (d-b))
      (V₂ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
      (oddRowScalarAction (K := K) (h := h) (n := n) hbd)
      (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) p))
    (u : Fin qS → MvPolynomial (Fin h ⊕ Fin n) K)
    (v : Fin qO → MvPolynomial (Fin h ⊕ Fin n) K)
    (hu : ∀ i,u i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d b)
    (hv : ∀ i,v i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d (b-1))
    (hrel : (∑ i,sumBiformMap (p.1 i)*u i)+(∑ i,sumBiformMap (p.2 i)*v i)=0) :
    u=0 ∧ v=0 := by
  have hU (i) : ∃ z : Forms K h b ⊗[K] Forms K n (d-b),sumBiformMap z=u i :=
    exists_sumBiformMap_of_homogeneous
      (by simpa only [Nat.add_sub_of_le hbd] using (show (u i).IsHomogeneous d from (hu i).1)) (hu i).2
  have hV (i) : ∃ z : Forms K h (b-1) ⊗[K] Forms K n (d-b+1),sumBiformMap z=v i :=
    exists_sumBiformMap_of_homogeneous
      (by simpa only [show (b-1)+(d-b+1)=d by omega] using (show (v i).IsHomogeneous d from (hv i).1)) (hv i).2
  choose U hU using hU
  choose V hV using hV
  have hzero : twoFamilyMultiplication (K := K)
      (P₁ := Forms K h 0 ⊗[K] Forms K n d)
      (P₂ := Forms K h 1 ⊗[K] Forms K n (d-1))
      (V₁ := Forms K h b ⊗[K] Forms K n (d-b))
      (V₂ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
      (oddRowScalarAction (K := K) (h := h) (n := n) hbd) (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) p (U,V)=0 := by
    apply sumBiformMap_injective
    rw [map_zero,twoFamilyMultiplication_apply,map_add,map_sum,map_sum]
    simpa only [oddRowScalarAction,oddRowLinearAction,sumBiformMap_action,hU,hV] using hrel
  have huv := hp (hzero.trans (map_zero _).symm)
  constructor
  · funext i
    have hi : U i=0 := congrArg (fun z => z.1 i) huv
    rw [← hU i,hi,map_zero]
    rfl
  · funext i
    have hi : V i=0 := congrArg (fun z => z.2 i) huv
    rw [← hV i,hi,map_zero]
    rfl

/-- The final scalar-free row has the same literal polynomial consequence. -/
theorem upper_odd_polynomial_row (hd : 1≤d)
    (p : Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1))
    (hp : Function.Injective (BilinearScalarFamily.multiplication (K := K)
      (F := Forms K h 1 ⊗[K] Forms K n (d-1))
      (V := Forms K h d ⊗[K] Forms K n 0)
      (W := Forms K h (d+1) ⊗[K] Forms K n (d-1))
      (biformAction (K := K) (h := h) (n := n) (a := 1) (b := d) (c := d-1) (e := 0)
        (r := d+1) (t := d-1) (by omega) (by omega)) p))
    (v : Fin qO → MvPolynomial (Fin h ⊕ Fin n) K)
    (hv : ∀ i,v i∈coefficientComponentSpace (Sum.elim (fun _ => 1) (fun _ => 0)) d d)
    (hrel : (∑ i,sumBiformMap (p i)*v i)=0) : v=0 := by
  have hV (i) : ∃ z : Forms K h d ⊗[K] Forms K n 0,sumBiformMap z=v i :=
    exists_sumBiformMap_of_homogeneous (by simpa only [add_zero] using (show (v i).IsHomogeneous d from (hv i).1)) (hv i).2
  choose V hV using hV
  have hzero : BilinearScalarFamily.multiplication (K := K)
      (F := Forms K h 1 ⊗[K] Forms K n (d-1))
      (V := Forms K h d ⊗[K] Forms K n 0)
      (W := Forms K h (d+1) ⊗[K] Forms K n (d-1))
      (biformAction (K := K) (h := h) (n := n) (a := 1) (b := d) (c := d-1) (e := 0)
        (r := d+1) (t := d-1) (by omega) (by omega)) p V=0 := by
    apply sumBiformMap_injective
    rw [map_zero,BilinearScalarFamily.multiplication_apply,map_sum]
    simpa only [sumBiformMap_action,hV] using hrel
  have hVzero := hp (hzero.trans (map_zero _).symm)
  funext i
  have hi : V i=0 := congrFun hVzero i
  rw [←hV i,hi,map_zero]
  rfl

end Froberg
