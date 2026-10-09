module

public import Froberg.GenericDimensions
public import Quartic.PolynomialRankOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! A generic frame is disjoint from any finite family of subspaces of
complementary dimension. This lets one fix a single quadratic output space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K V I : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {H : ℕ}

lemma frame_disjoint_of_quotient_independent (R : Submodule K V) (f : Fin H → V)
    (hf : LinearIndependent K (fun i => R.mkQ (f i))) :
    Disjoint (Submodule.span K (Set.range f)) R := by
  rw [Submodule.disjoint_def]
  intro x hx hR
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  have hz : ∑ i,a i • R.mkQ (f i)=0 := by
    simp_rw [←map_smul]
    rw [←map_sum,ha]
    exact (Submodule.Quotient.mk_eq_zero R).mpr hR
  have ha0 := Fintype.linearIndependent_iff.mp hf a hz
  rw [←ha]
  simp only [ha0,zero_smul,Finset.sum_const_zero]

/-- This is an open in unrestricted frame coefficients, so it intersects
any independently constructed nonempty frame open. -/
theorem frame_disjoint_principal_open (R : I → Submodule K V)
    (hcap : ∀ i,H+finrank K (R i)≤finrank K V) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → V))) K,
      (∃ x,eval x D≠0) ∧
      ∀ f : Fin H → V,eval ((Module.finBasis K _).equivFun f) D≠0 →
        ∀ i,Disjoint (Submodule.span K (Set.range f)) (R i) := by
  classical
  let e := (Module.finBasis K (Fin H → V)).equivFun
  have hlocal (i : I) :
      ∃ D : MvPolynomial (Fin (finrank K (Fin H → V))) K,
        (∃ x,eval x D≠0) ∧
        ∀ f : Fin H → V,eval (e f) D≠0 →
          LinearIndependent K (fun j => (R i).mkQ (f j)) := by
    have hdim : H≤finrank K (V ⧸ R i) := by
      have hd := (R i).finrank_quotient_add_finrank
      have hh := hcap i
      omega
    obtain ⟨g,hg⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := V ⧸ R i) hdim
    choose f hf using fun j => (R i).mkQ_surjective (g j)
    have hpoly (j : Fin H) : IsPolynomialFamily (fun x => (R i).mkQ (e.symm x j)) :=
      isPolynomialFamily_linear ((R i).mkQ.comp ((LinearMap.proj j).comp e.symm.toLinearMap))
    obtain ⟨D,hD,hgood⟩ := independent_polynomial_principal_open
      (fun j x => (R i).mkQ (e.symm x j)) hpoly (e f)
      (by simpa only [LinearEquiv.symm_apply_apply,hf] using hg)
    exact ⟨D,⟨e f,hD⟩,fun f hf => by simpa only [LinearEquiv.symm_apply_apply] using hgood (e f) hf⟩
  choose D hD hgood using hlocal
  have hnz (i : I) : D i≠0 := by
    obtain ⟨x,hx⟩ := hD i
    intro hz
    exact hx (by rw [hz,map_zero])
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ i,D i,⟨x,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  intro f hf i
  rw [map_prod] at hf
  exact frame_disjoint_of_quotient_independent (R i) f
    (hgood i f (Finset.prod_ne_zero_iff.mp hf i (Finset.mem_univ _)))

end Froberg
