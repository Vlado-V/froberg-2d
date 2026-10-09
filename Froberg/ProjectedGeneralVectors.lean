module

public import Froberg.GeneralPositionVectors
public import Quartic.PolynomialRankOpen
public import Quartic.PolynomialBilinearCoordinates

@[expose] public section

/-! A common generic vector family stays in general position after any
fixed finite list of linear quotients. These are opens in the original,
unrestricted coefficient family. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.PolynomialBilinearCoordinates
variable {K V W : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {m : ℕ}

/-- Every fixed linear quotient admits vectors whose small projected
subfamilies are independent, up to the exact quotient-image dimension. -/
theorem exists_projected_general_vectors (F : V →ₗ[K] W) :
    ∃ v : Fin m → V, ∀ S : Finset (Fin m), S.card≤finrank K F.range →
      LinearIndependent K (fun i : S => F (v i.val)) := by
  classical
  obtain ⟨w,hw⟩ := GeneralPositionVectors.exists_small_subfamilies_independent
    (K := K) (α := Fin m) (finrank K F.range)
  let e := (coordinates K F.range).symm
  have hpre (i : Fin m) : ∃ x : V, F x=(e (w i)).val := (e (w i)).property
  choose v hv using hpre
  refine ⟨v,?_⟩
  intro S hS
  have hli := ((hw S hS).map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)).map'
    F.range.subtype F.range.ker_subtype
  simpa only [Function.comp_def,LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply,← hv] using hli

/-- Projected general position holds on a principal open in the actual
vector coefficients; its bound is the rank of the specified projection. -/
theorem projected_general_vectors_open (F : V →ₗ[K] W) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → V))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 →
        ∀ S : Finset (Fin m),S.card≤finrank K F.range →
          LinearIndependent K (fun i : S => F ((coordinates K (Fin m → V)).symm x i.val)) := by
  classical
  obtain ⟨v,hv⟩ := exists_projected_general_vectors (m := m) F
  let C := {S : Finset (Fin m) // S.card≤finrank K F.range}
  have hlocal (c : C) :
      ∃ D : MvPolynomial (Fin (finrank K (Fin m → V))) K,
        eval (coordinates K _ v) D≠0 ∧ ∀ x,eval x D≠0 →
          LinearIndependent K (fun i : c.val => F ((coordinates K (Fin m → V)).symm x i.val)) := by
    let e := (Fintype.equivFin c.val).symm
    let q : Fin (Fintype.card c.val) → (Fin (finrank K (Fin m → V)) → K) → W :=
      fun j x => F ((coordinates K (Fin m → V)).symm x (e j).val)
    have hpoly (j) : IsPolynomialFamily (q j) :=
      isPolynomialFamily_linear (F.comp ((LinearMap.proj (e j).val).comp
        (coordinates K (Fin m → V)).symm.toLinearMap))
    have hq : LinearIndependent K (fun j => q j (coordinates K _ v)) := by
      simpa only [q,Function.comp_def,LinearEquiv.symm_apply_apply] using (hv c.val c.property).comp e e.injective
    obtain ⟨D,hD,hgood⟩ := independent_polynomial_principal_open q hpoly _ hq
    refine ⟨D,hD,?_⟩
    intro x hx
    have hh := (hgood x hx).comp e.symm e.symm.injective
    simpa only [q,Function.comp_def,Equiv.apply_symm_apply] using hh
  choose D hD hgood using hlocal
  refine ⟨∏ c,D c,⟨coordinates K _ v,?_⟩,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun c _ => hD c)
  intro x hx S hS
  rw [map_prod] at hx
  exact hgood ⟨S,hS⟩ x (Finset.prod_ne_zero_iff.mp hx ⟨S,hS⟩ (Finset.mem_univ _))

/-- Finitely many projection requirements use one and the same vector tuple. -/
theorem finite_projected_general_vectors_open {I : Type*} [Fintype I]
    (F : I → V →ₗ[K] W) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → V))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 →
        ∀ i (S : Finset (Fin m)),S.card≤finrank K (F i).range →
          LinearIndependent K (fun j : S => F i ((coordinates K (Fin m → V)).symm x j.val)) := by
  classical
  choose D hD hgood using fun i => projected_general_vectors_open (m := m) (F i)
  have hne (i) : D i≠0 := by
    obtain ⟨x,hx⟩ := hD i
    intro hz
    exact hx (by rw [hz,map_zero])
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hne
  refine ⟨∏ i,D i,⟨x,?_⟩,?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  intro x hx i
  rw [map_prod] at hx
  exact hgood i x (Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _))

end Froberg
