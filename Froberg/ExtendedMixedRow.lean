module

public import Froberg.LowerMixedRow

@[expose] public section

/-! Exact core rows persist on adjoining private variables: a relation with
a core-only inhomogeneous term has no nonzero private coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial Quartic.FreeCoefficients
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {a z q s d : ℕ}

lemma freeCoeff_rename_core (β : Fin z →₀ ℕ) (f : Poly K a) :
    freeCoeff β (rename (Fin.castAdd z) f)=if β=0 then f else 0 := by
  rw [←liftCoeff_zero_eq_rename,freeCoeff_liftCoeff]
  simp only [eq_comm]

lemma eq_rename_freeCoeff_zero (f : Poly K (a+z))
    (hf : ∀ β : Fin z →₀ ℕ,β≠0 → freeCoeff β f=0) :
    f=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) f) := by
  apply MvPolynomial.ext
  intro γ
  rw [←merge_core_free γ,←freeCoeff_coeff,←freeCoeff_coeff,freeCoeff_rename_core]
  by_cases hβ : freeExponent γ=0
  · simp [hβ]
  · simp [hβ,hf _ hβ]

/-- The private-variable extension introduces no new lower coefficients.
The returned relation is literally the original core relation, not an
abstractly isomorphic kernel. -/
theorem extended_mixed_relation_core (hsd : s≤d)
    (E : I → J → Poly K a) (Q : Fin q → Poly K a) (C : J → Poly K a)
    (hbelow : ∀ t,0<t → t ≤ s →
      ∀ (x : Fin q → J → Poly K a) (p : I → Poly K a),
        (∀ i j,(x i j).IsHomogeneous (s-t)) →
        (∀ i,(p i).IsHomogeneous (d-t)) →
        (∀ j,(∑ i,Q i*x i j)+(∑ k,E k j*p k)=0) → x=0 ∧ p=0)
    (hEinj : ∀ t,t<d → Function.Injective (corePolynomialMatrix (t := t) (fun j i => E i j)))
    (x : Fin q → J → Poly K (a+z)) (p : I → Poly K (a+z))
    (hx : ∀ i j,(x i j).IsHomogeneous s)
    (hp : ∀ i,(p i).IsHomogeneous d)
    (hrel : ∀ j,(∑ i,rename (Fin.castAdd z) (Q i)*x i j)+
      (∑ k,rename (Fin.castAdd z) (E k j)*p k)+rename (Fin.castAdd z) (C j)=0) :
    (∀ i j,x i j=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) (x i j))) ∧
    (∀ i,p i=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) (p i))) ∧
    ∀ j,(∑ i,Q i*freeCoeff (0 : Fin z →₀ ℕ) (x i j))+
      (∑ k,E k j*freeCoeff (0 : Fin z →₀ ℕ) (p k))+C j=0 := by
  have hcoeff (β : Fin z →₀ ℕ) (j : J) :
      (∑ i,Q i*freeCoeff β (x i j))+(∑ k,E k j*freeCoeff β (p k))+
        (if β=0 then C j else 0)=0 := by
    have h := congrArg (freeCoeff β) (hrel j)
    simpa only [map_add,map_sum,map_zero,freeCoeff_rename_mul,freeCoeff_rename_core] using h
  have hz (β : Fin z →₀ ℕ) (hβ : β≠0) :
      (∀ i j,freeCoeff β (x i j)=0) ∧ (∀ i,freeCoeff β (p i)=0) := by
    have hbpos : 0<β.degree := Nat.pos_of_ne_zero (by intro h; exact hβ ((Finsupp.degree_eq_zero_iff β).mp h))
    have hrow (j : J) : (∑ i,Q i*freeCoeff β (x i j))+
        (∑ k,E k j*freeCoeff β (p k))=0 := by
      simpa only [if_neg hβ,add_zero] using hcoeff β j
    by_cases hbs : β.degree ≤ s
    · obtain ⟨hxx,hpp⟩ := hbelow β.degree hbpos hbs
        (fun i j => freeCoeff β (x i j)) (fun k => freeCoeff β (p k))
        (fun i j => freeCoeff_homogeneous _ (hx i j) β)
        (fun k => freeCoeff_homogeneous _ (hp k) β) hrow
      exact ⟨fun i j => congrFun (congrFun hxx i) j,fun k => congrFun hpp k⟩
    · have hxx (i) (j) : freeCoeff β (x i j)=0 :=
        freeCoeff_eq_zero_of_degree_lt _ (hx i j) β (by omega)
      refine ⟨hxx,?_⟩
      by_cases hbd : β.degree≤d
      · let pβ : I → Forms K a (d-β.degree) := fun k =>
          ⟨freeCoeff β (p k),freeCoeff_homogeneous _ (hp k) β⟩
        have hzero : corePolynomialMatrix (fun j i => E i j) pβ=0 := by
          funext j
          simpa only [hxx,mul_zero,Finset.sum_const_zero,zero_add,
            corePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,pβ,Pi.zero_apply] using hrow j
        have hpzero := hEinj (d-β.degree) (by omega) (hzero.trans (map_zero _).symm)
        exact fun k => congrArg Subtype.val (congrFun hpzero k)
      · exact fun k => freeCoeff_eq_zero_of_degree_lt _ (hp k) β (by omega)
  refine ⟨fun i j => eq_rename_freeCoeff_zero _ (fun β hβ => (hz β hβ).1 i j),
    fun i => eq_rename_freeCoeff_zero _ (fun β hβ => (hz β hβ).2 i),?_⟩
  intro j
  simpa only [ite_true] using hcoeff 0 j

end Froberg
