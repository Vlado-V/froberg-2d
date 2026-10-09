module

public import Froberg.LowerRelationComparison
public import Froberg.PrivateCoreCoefficients

@[expose] public section

/-! A scalar/new-layer relation one degree below its exact endpoint must
vanish. This is the core argument used before adjoining private variables. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {n q s d : ℕ}

/-- Compare two independent linear lifts to the endpoint. Only the actual
constant-column part of endpoint exactness is needed. -/
theorem lower_mixed_row_zero (hs : 1 ≤ s) (hd : 1≤d)
    (E : I → J → Poly K n) (Q : Fin q → Poly K n)
    (hlinear : Function.Injective (linearVectorCombination E))
    (hinj : Function.Injective (corePolynomialMatrix (t := d-1) (fun j i => E i j)))
    (ell : Fin 2 → Forms K n 1) (hell : LinearIndependent K ell)
    (hendpoint : ∀ (x : Fin q → J → Poly K n) (p : I → Poly K n),
      (∀ i j,(x i j).IsHomogeneous s) → (∀ i,(p i).IsHomogeneous d) →
      (∀ j,(∑ i,Q i*x i j)+(∑ a,E a j*p a)=0) →
      ∃ C : Fin q → I → K,∀ i j,x i j=∑ a,C i a • E a j)
    (x : Fin q → J → Poly K n) (p : I → Poly K n)
    (hx : ∀ i j,(x i j).IsHomogeneous (s-1))
    (hp : ∀ i,(p i).IsHomogeneous (d-1))
    (hrel : ∀ j,(∑ i,Q i*x i j)+(∑ a,E a j*p a)=0) : x=0 ∧ p=0 := by
  have hstep (l : Fin 2) : ∃ C : Fin q → I → K,
      ∀ i j,(ell l).val*x i j=∑ a,C i a • E a j := by
    apply hendpoint (fun i j => (ell l).val*x i j) (fun a => (ell l).val*p a)
    · intro i j
      simpa only [show 1+(s-1)=s by omega] using (ell l).property.mul (hx i j)
    · intro i
      simpa only [show 1+(d-1)=d by omega] using (ell l).property.mul (hp i)
    · intro j
      calc
        (∑ i,Q i*((ell l).val*x i j))+(∑ a,E a j*((ell l).val*p a)) =
            (ell l).val*((∑ i,Q i*x i j)+(∑ a,E a j*p a)) := by
          rw [mul_add,Finset.mul_sum,Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl
            intro i _
            ring
          · apply Finset.sum_congr rfl
            intro i _
            ring
        _ = 0 := by rw [hrel,mul_zero]
  choose C hC using hstep
  have hxzero : x=0 := by
    funext i
    exact (lower_relation_comparison E hlinear ell hell (x i) (C 0 i) (C 1 i)
      (hC 0 i) (hC 1 i)).1
  refine ⟨hxzero,?_⟩
  let p' : I → Forms K n (d-1) := fun i => ⟨p i,hp i⟩
  have hpzero : corePolynomialMatrix (fun j i => E i j) p'=0 := by
    funext j
    have hh := hrel j
    rw [hxzero] at hh
    simpa only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,zero_add,
      corePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,p'] using hh
  have hp' : p'=0 := hinj (hpzero.trans (map_zero _).symm)
  funext i
  exact congrArg Subtype.val (congrFun hp' i)

/-- Vanishing at a fixed lower row implies vanishing in every still lower
row by multiplication with one nonzero linear form. -/
theorem mixed_row_lower_zero {A B a b : ℕ}
    (E : I → J → Poly K n) (Q : Fin q → Poly K n)
    (hzero : ∀ (x : Fin q → J → Poly K n) (p : I → Poly K n),
      (∀ i j,(x i j).IsHomogeneous A) → (∀ i,(p i).IsHomogeneous B) →
      (∀ j,(∑ i,Q i*x i j)+(∑ k,E k j*p k)=0) → x=0 ∧ p=0)
    (ell : Forms K n 1) (hell : ell≠0)
    (ha : a≤A) (hb : b≤B) (hab : A-a=B-b)
    (x : Fin q → J → Poly K n) (p : I → Poly K n)
    (hx : ∀ i j,(x i j).IsHomogeneous a)
    (hp : ∀ i,(p i).IsHomogeneous b)
    (hrel : ∀ j,(∑ i,Q i*x i j)+(∑ k,E k j*p k)=0) : x=0 ∧ p=0 := by
  let l : Poly K n := ell.val^(A-a)
  have hl : l≠0 := pow_ne_zero _ (fun h => hell (Subtype.ext h))
  have hld : l.IsHomogeneous (A-a) := by
    simpa only [one_mul] using ell.property.pow (A-a)
  have hrel' (j) : (∑ i,Q i*(l*x i j))+(∑ k,E k j*(l*p k))=0 := by
    calc
      _ = l*((∑ i,Q i*x i j)+(∑ k,E k j*p k)) := by
        rw [mul_add,Finset.mul_sum,Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          ring
        · apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 0 := by rw [hrel,mul_zero]
  obtain ⟨hz,hz'⟩ := hzero (fun i j => l*x i j) (fun k => l*p k)
    (fun i j => by simpa only [Nat.sub_add_cancel ha] using hld.mul (hx i j))
    (fun k => by simpa only [hab,Nat.sub_add_cancel hb] using hld.mul (hp k)) hrel'
  constructor
  · funext i j
    exact (mul_eq_zero.mp (congrFun (congrFun hz i) j)).resolve_left hl
  · funext k
    exact (mul_eq_zero.mp (congrFun hz' k)).resolve_left hl

end Froberg
