module

public import Froberg.SymmetricIndependence

@[expose] public section

/-! Independence of unordered products detects exactly the alternating
constant matrices, including the diagonal condition in characteristic two. -/
noncomputable section
namespace Froberg
open Finset
attribute [local instance] Classical.propDecidable
variable {K A I : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype I]

/-- The two orientations of a nondiagonal unordered pair contribute once
each; a diagonal contributes once. -/
theorem sum_unordered_pair_fiber (B : I → I → K) (a b : I) :
    (∑ i,∑ j,if s(i,j)=s(a,b) then B i j else 0)=
      if a=b then B a a else B a b+B b a := by
  classical
  by_cases hab : a=b
  · subst b
    simp only [Sym2.eq_iff,or_self,if_pos rfl]
    simp only [ite_and]
    simp
  · rw [if_neg hab]
    have hterm (i j : I) :
        (if s(i,j)=s(a,b) then B i j else 0)=
          (if i=a then if j=b then B i j else 0 else 0)+
          (if i=b then if j=a then B i j else 0 else 0) := by
      simp only [Sym2.eq_iff]
      by_cases hia : i=a <;> by_cases hib : i=b <;>
        by_cases hja : j=a <;> by_cases hjb : j=b <;> simp_all
    simp_rw [hterm,sum_add_distrib]
    simp

/-- The coefficient of any independent selected unordered product must be
zero in a vanishing constant-matrix product. -/
theorem matrix_product_pair_coefficient_zero
    (q : I → A) (P : Sym2 I → Prop) [DecidablePred P]
    (hP : LinearIndependent K (fun p : {p : Sym2 I // P p} => pairProducts q p.val))
    (B : I → I → K) (hB : ∀ i j,¬P s(i,j) → B i j=0)
    (hzero : ∑ i,∑ j,B i j • (q i*q j)=0)
    (p : {p : Sym2 I // P p}) :
    (∑ i,∑ j,if s(i,j)=p.val then B i j else 0)=0 := by
  classical
  obtain ⟨L,hL⟩ := (Finsupp.linearCombination K
    (fun p : {p : Sym2 I // P p} => pairProducts q p.val)).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hP)
  have hLp (p : {p : Sym2 I // P p}) : L (pairProducts q p.val)=Finsupp.single p 1 := by
    have h := LinearMap.congr_fun hL (Finsupp.single p 1)
    simpa only [LinearMap.comp_apply,Finsupp.linearCombination_single,one_smul,LinearMap.id_apply] using h
  have hterm (i j : I) : B i j • L (q i*q j) p =
      if s(i,j)=p.val then B i j else 0 := by
    by_cases hij : P s(i,j)
    · have heq : L (q i*q j)=Finsupp.single ⟨s(i,j),hij⟩ 1 := hLp ⟨s(i,j),hij⟩
      rw [heq]
      simp only [Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,Subtype.ext_iff]
    · have hne : s(i,j)≠p.val := fun h => hij (h.symm ▸ p.property)
      simp [hB i j hij,hne]
  have h := congrArg (fun x => L x p) hzero
  simpa only [map_sum,map_smul,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.smul_apply,map_zero,Finsupp.zero_apply,hterm] using h

/-- A zero product matrix is alternating on every selected pair. -/
theorem matrix_product_alternating
    (q : I → A) (P : Sym2 I → Prop) [DecidablePred P]
    (hP : LinearIndependent K (fun p : {p : Sym2 I // P p} => pairProducts q p.val))
    (B : I → I → K) (hB : ∀ i j,¬P s(i,j) → B i j=0)
    (hzero : ∑ i,∑ j,B i j • (q i*q j)=0) :
    (∀ i j,P s(i,j) → B i j = -B j i) ∧ (∀ i,P s(i,i) → B i i=0) := by
  classical
  have hcoeff (i j : I) (hij : P s(i,j)) :=
    matrix_product_pair_coefficient_zero q P hP B hB hzero ⟨s(i,j),hij⟩
  constructor
  · intro i j hij
    have h := hcoeff i j hij
    rw [sum_unordered_pair_fiber] at h
    by_cases heq : i=j
    · subst j
      simp only [if_true] at h
      simp [h]
    · rw [if_neg heq] at h
      exact eq_neg_of_add_eq_zero_left h
  · intro i hii
    have h := hcoeff i i hii
    simpa only [sum_unordered_pair_fiber,if_true] using h

end Froberg
