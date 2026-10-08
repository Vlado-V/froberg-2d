import Froberg.SymmetricIndependence
import Froberg.GeneralPositionVectors

/-! Scalar coefficient families with independent products separately for each
unordered pair of output labels.  Joint independence of all scalar groups is
not required. -/
noncomputable section
namespace Froberg
open Module Finset
variable {K : Type} [Field K]
variable {B : Type*} [CommRing B] [Algebra K B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- The source products attached to a specified unordered output pair. -/
abbrev ScalarPairFiber (δ : Sym2 ι) :=
  {p : Sym2 (ι × Fin r) // Sym2.map Prod.fst p = δ}

def scalarFiberLabels (δ : Sym2 ι) : Finset (ι × Fin r) :=
  δ.toFinset.product Finset.univ

theorem card_scalarFiberLabels (δ : Sym2 ι) : (scalarFiberLabels (r := r) δ).card ≤ 2*r := by
  simp only [scalarFiberLabels, Finset.product_eq_sprod]
  rw [card_product, card_univ, Fintype.card_fin, Sym2.card_toFinset]
  split_ifs <;> omega

@[simp] theorem mem_scalarFiberLabels (δ : Sym2 ι) (i : ι × Fin r) :
    i ∈ scalarFiberLabels δ ↔ i.1 ∈ δ := by
  simp [scalarFiberLabels, Sym2.mem_toFinset]

theorem pairProducts_map {α β : Type*} (q : β → B) (f : α → β) (p : Sym2 α) :
    pairProducts q (Sym2.map f p) = pairProducts (q ∘ f) p := by
  induction p using Sym2.inductionOn with | _ i j => rfl

/-- A full-spark scalar family gives all diagonal and cross-product injections
needed by the separated coefficient construction. -/
theorem scalar_pair_fiber_independent (C : Submodule K B)
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (c : ι × Fin r → C)
    (hc : ∀ T : Finset (ι × Fin r), T.card ≤ 2*r →
      LinearIndependent K (fun i : T => c i.val)) (δ : Sym2 ι) :
    LinearIndependent K (fun p : ScalarPairFiber (r := r) δ =>
      pairProducts (fun i => (c i).val) p.val) := by
  classical
  let T := scalarFiberLabels (r := r) δ
  have hT : LinearIndependent K (fun i : T => c i.val) := hc T (card_scalarFiberLabels δ)
  have hp := linearIndependent_pairProducts_in_subspace C hC (fun i : T => c i.val) hT
  have hlabels (p : ScalarPairFiber (r := r) δ) : ∀ i ∈ p.val, i ∈ T := by
    intro i hi
    apply (mem_scalarFiberLabels δ i).mpr
    have h : i.1 ∈ Sym2.map Prod.fst p.val := Sym2.mem_map.mpr ⟨i,hi,rfl⟩
    simpa only [p.property] using h
  let attach (p : ScalarPairFiber (r := r) δ) : Sym2 T := p.val.attachWith (hlabels p)
  have hback (p : ScalarPairFiber (r := r) δ) : Sym2.map Subtype.val (attach p) = p.val :=
    Sym2.attachWith_map_subtypeVal (hlabels p)
  have hi : Function.Injective attach := by
    intro p q hpq
    apply Subtype.ext
    rw [← hback p, ← hback q, hpq]
  have h := hp.comp attach hi
  convert h using 1
  funext p
  rw [← hback p, pairProducts_map]
  rfl

/-- Arbitrarily many scalar groups, each of size r, with pairwise independent
unions exist whenever 2r is at most the scalar-space dimension. -/
theorem exists_scalar_pair_fiber_independent [Infinite K] (C : Submodule K B)
    [Module.Finite K C] (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hr : 2*r ≤ finrank K C) :
    ∃ c : ι × Fin r → C, ∀ δ : Sym2 ι,
      LinearIndependent K (fun p : ScalarPairFiber (r := r) δ =>
        pairProducts (fun i => (c i).val) p.val) := by
  classical
  obtain ⟨v,hv⟩ := GeneralPositionVectors.exists_small_subfamilies_independent
    (K := K) (α := ι × Fin r) (finrank K C)
  let e := (Module.finBasis K C).equivFun
  let c : ι × Fin r → C := fun i => e.symm (v i)
  refine ⟨c, scalar_pair_fiber_independent C hC c ?_⟩
  intro T hT
  exact (hv T (hT.trans hr)).map' e.symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.symm.injective)

end Froberg
