import Froberg.GenericDimensions
import Quartic.PolynomialRankOpen
import Froberg.SymmetricIndependence
import Froberg.QuadraticBlockSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! A product-independent family extends to a full output frame. Its product
minor stays nonzero on a principal open in that frame's actual coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} {V σ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Extend a finite independent family while preserving its literal prefix. -/
theorem extend_independent_prefix {k H : ℕ} (q : Fin k → V)
    (hq : LinearIndependent K q) (hkH : k≤H) (hH : H≤finrank K V) :
    ∃ f : Fin H → V,LinearIndependent K f ∧ ∀ i,f (Fin.castLE hkH i)=q i := by
  have aux : ∀ t,k+t≤finrank K V →
      ∃ f : Fin (k+t) → V,LinearIndependent K f ∧
        ∀ i,f (Fin.castLE (Nat.le_add_right k t) i)=q i := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨q,hq,fun _ => rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨f,hf,hprefix⟩ := ih (by omega)
      obtain ⟨x,hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hf (by omega)
      refine ⟨Fin.snoc f x,hx,?_⟩
      intro i
      have he : Fin.castLE (Nat.le_add_right k (t+1)) i=
          (Fin.castLE (Nat.le_add_right k t) i).castSucc := by ext; rfl
      rw [he,Fin.snoc_castSucc]
      exact hprefix i
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hkH
  exact aux t hH

/-- The small-degree output requirement is a genuine open condition on an
otherwise arbitrary full output frame; the subfamily is its fixed prefix. -/
theorem output_frame_product_prefix_open [Infinite K] {k H : ℕ}
    (j : V →ₗ[K] MvPolynomial σ K) (q : Fin k → V)
    (hq : LinearIndependent K (pairProducts (fun i => j (q i))))
    (hkH : k≤H) (hH : H≤finrank K V) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → V))) K,
      (∃ f : Fin H → V,eval ((Module.finBasis K _).equivFun f) D≠0) ∧
      ∀ f : Fin H → V,eval ((Module.finBasis K _).equivFun f) D≠0 →
        LinearIndependent K f ∧
        LinearIndependent K (pairProducts (fun i => j (f (Fin.castLE hkH i)))) := by
  classical
  have hqi : LinearIndependent K q :=
    LinearIndependent.of_comp j (linearIndependent_of_pairProducts _ hq)
  obtain ⟨f₀,hf₀,hprefix⟩ := extend_independent_prefix q hqi hkH hH
  let e := (Module.finBasis K (Fin H → V)).equivFun
  let a₀ := e f₀
  let c : Fin (Fintype.card (Sym2 (Fin k))) ≃ Sym2 (Fin k) :=
    (Fintype.equivFin _).symm
  have hlinear (i : Fin H) : IsPolynomialFamily (fun a => e.symm a i) :=
    isPolynomialFamily_linear ((LinearMap.proj i).comp e.symm.toLinearMap)
  have hprod (p : Sym2 (Fin k)) : IsPolynomialFamily
      (fun a => pairProducts (fun i => j (e.symm a (Fin.castLE hkH i))) p) := by
    induction p using Sym2.inductionOn with
    | _ i l =>
      exact (hlinear _).bilinear (hlinear _)
        ((LinearMap.mul K (MvPolynomial σ K)).compl₁₂ j j)
  obtain ⟨D₁,hD₁,hgood₁⟩ := independent_polynomial_principal_open
    (fun i a => e.symm a i) hlinear a₀ (by simpa only [a₀,LinearEquiv.symm_apply_apply] using hf₀)
  obtain ⟨D₂,hD₂,hgood₂⟩ := independent_polynomial_principal_open
    (fun i a => pairProducts (fun l => j (e.symm a (Fin.castLE hkH l))) (c i))
    (fun i => hprod (c i)) a₀ (by
      simpa only [a₀,LinearEquiv.symm_apply_apply,hprefix,Function.comp_def] using hq.comp c c.injective)
  refine ⟨D₁*D₂,⟨f₀,by simpa only [map_mul] using mul_ne_zero hD₁ hD₂⟩,?_⟩
  intro f hf
  obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp (show eval (e f) D₁*eval (e f) D₂≠0 by
    simpa only [map_mul] using hf)
  refine ⟨by simpa only [LinearEquiv.symm_apply_apply] using hgood₁ (e f) h₁,?_⟩
  have hh := (hgood₂ (e f) h₂).comp c.symm c.symm.injective
  simpa only [Function.comp_def,LinearEquiv.symm_apply_apply,Equiv.apply_symm_apply] using hh

/-- A generic quadratic output frame of any sufficient dimension contains
an H2 subfamily with its full product-independent dimension. -/
theorem quadratic_output_frame_open {K : Type} [Field K] [Infinite K]
    {h H : ℕ} (hh : 65≤h) (hkH : 5*h^2/32≤H)
    (hH : H≤finrank K (Forms K h 2)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin H → Forms K h 2))) K,
      (∃ f : Fin H → Forms K h 2,eval ((Module.finBasis K _).equivFun f) D≠0) ∧
      ∀ f : Fin H → Forms K h 2,eval ((Module.finBasis K _).equivFun f) D≠0 →
        LinearIndependent K f ∧
        LinearIndependent K (pairProducts (fun i : Fin (5*h^2/32) =>
          (f (Fin.castLE hkH i)).val)) := by
  obtain ⟨q,hq,hprod⟩ := QuadraticBlocks.exists_independent_quadrics (K := K)
    (h := h) (w := h/2) (m := 5*h^2/32) (by omega)
    (QuadraticBlocks.required_quadratic_count hh)
  exact output_frame_product_prefix_open (Forms K h 2).subtype
    (fun i => ⟨q i,hq i⟩) hprod hkH hH

end Froberg
