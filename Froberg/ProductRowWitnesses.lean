import Froberg.ProductRowGluing
import Froberg.BiformWitnesses

/-! Insert actual cross and diagonal polynomial witnesses into the single
family of layer generators used by a formal product row. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] {σ : Type*}
variable {J : Finset ℕ} {R : ℕ}

theorem cross_row_witness (e : ℕ → ℕ) (w : σ → ℕ) (r : Row J R)
    (hne : r.val.val ≠ R-r.val.val)
    (f : Fin (e r.val.val) → MvPolynomial σ K)
    (g : Fin (e (R-r.val.val)) → MvPolynomial σ K)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w r.val.val)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w 0)
    (hp : LinearIndependent K (fun p : Fin (e r.val.val) × Fin (e (R-r.val.val)) => f p.1 * g p.2)) :
    ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial σ K,
      (∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j)) ∧
      LinearIndependent K (products e q r) := by
  classical
  let q : (j : ℕ) → Fin (e j) → MvPolynomial σ K :=
    Function.update (Function.update (fun _ => 0) (R-r.val.val) g) r.val.val f
  have hleft : q r.val.val = f := Function.update_self _ _ _
  have hright : q (R-r.val.val) = g := by
    simp only [q,Function.update_of_ne hne.symm,Function.update_self]
  have hsmall : 2*r.val.val<R := by have := r.property.2.2; omega
  have hlarge : R<2*(R-r.val.val) := by omega
  refine ⟨q,?_,?_⟩
  · intro j hj i
    by_cases hlj : j=r.val.val
    · subst j
      rw [hleft]
      simpa only [assignedDegree,if_pos hsmall] using hf i
    · by_cases hrj : j=R-r.val.val
      · subst j
        rw [hright]
        simpa [assignedDegree,show ¬2*(R-r.val.val)<R by omega,
          show ¬2*(R-r.val.val)=R by omega] using hg i
      · have hz : q j i = 0 := by simp [q,Function.update_of_ne hlj,Function.update_of_ne hrj]
        rw [hz]
        exact isWeightedHomogeneous_zero K w _
  · let c : Columns e r ≃ Fin (e r.val.val) × Fin (e (R-r.val.val)) := Equiv.cast (if_neg hne)
    have hh := hp.comp c c.injective
    convert hh using 1
    funext p
    simp only [products,dif_neg hne,hleft,hright,Function.comp_apply]
    rfl

theorem diagonal_row_witness (e : ℕ → ℕ) (w : σ → ℕ) (r : Row J R)
    (heq : r.val.val = R-r.val.val)
    (f : Fin (e r.val.val) → MvPolynomial σ K)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (r.val.val/2))
    (hp : LinearIndependent K (pairProducts f)) :
    ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial σ K,
      (∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j)) ∧
      LinearIndependent K (products e q r) := by
  classical
  let q : (j : ℕ) → Fin (e j) → MvPolynomial σ K := Function.update (fun _ => 0) r.val.val f
  have hleft : q r.val.val = f := Function.update_self _ _ _
  have htwo : 2*r.val.val=R := by have := r.property.2.2; omega
  refine ⟨q,?_,?_⟩
  · intro j hj i
    by_cases hlj : j=r.val.val
    · subst j
      rw [hleft]
      simpa [assignedDegree,htwo] using hf i
    · have hz : q j i = 0 := by simp [q,Function.update_of_ne hlj]
      rw [hz]
      exact isWeightedHomogeneous_zero K w _
  · let c : Columns e r ≃ Sym2 (Fin (e r.val.val)) := Equiv.cast (if_pos heq)
    have hh := hp.comp c c.injective
    convert hh using 1
    funext p
    simp only [products,dif_pos heq,hleft,Function.comp_apply]
    rfl

/-- The exact cross/diagonal witness interface sufficient for an injective
common-family product row. -/
theorem exists_product_row_from_pair_witnesses (e : ℕ → ℕ) (w : σ → ℕ)
    (heven : ∀ j ∈ J, Even j)
    (hdiag : ∀ r : Row J R, r.val.val = R-r.val.val →
      ∃ f : Fin (e r.val.val) → MvPolynomial σ K,
        (∀ i, (f i).IsWeightedHomogeneous w (r.val.val/2)) ∧
        LinearIndependent K (pairProducts f))
    (hcross : ∀ r : Row J R, r.val.val ≠ R-r.val.val →
      ∃ (f : Fin (e r.val.val) → MvPolynomial σ K)
        (g : Fin (e (R-r.val.val)) → MvPolynomial σ K),
        (∀ i, (f i).IsWeightedHomogeneous w r.val.val) ∧
        (∀ i, (g i).IsWeightedHomogeneous w 0) ∧
        LinearIndependent K (fun p : Fin (e r.val.val) × Fin (e (R-r.val.val)) => f p.1 * g p.2)) :
    ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial σ K,
      (∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j)) ∧
      Function.Injective (multiplication e q J R) := by
  apply exists_injective_product_row e w heven
  intro r
  by_cases heq : r.val.val = R-r.val.val
  · obtain ⟨f,hf,hp⟩ := hdiag r heq
    exact diagonal_row_witness e w r heq f hf hp
  · obtain ⟨f,g,hf,hg,hp⟩ := hcross r heq
    exact cross_row_witness e w r heq f g hf hg hp

end Froberg.ProductRows
