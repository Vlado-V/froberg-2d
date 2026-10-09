module

public import Froberg.UnequalCrossPair
public import Froberg.SingleCrossRow
public import Froberg.SmallFourthParameters
public import Froberg.PreparedEmptyProfileRow

@[expose] public section

/-! The literal row-six cross witness, on the same full prepared parameter
space as the scalar, sparse and diagonal witnesses. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem exists_cross_row_profile_parameter
    (R j : ℕ) (hj : j≠R-j)
    (honly : ∀ r : ProductRows.Row J R,ProductRows.Columns counts r → r.val.val=j)
    (f : Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (g : Fin (counts (R-j)) → MvPolynomial (σ ⊕ Fin n) K)
    (hf : ∀ i,f i∈biformImage (O j) (Forms K n (d-j)))
    (hg : ∀ i,g i∈biformImage (O (R-j)) (Forms K n (d-(R-j))))
    (hi : LinearIndependent K (fun p : Fin (counts j) × Fin (counts (R-j)) => f p.1*g p.2))
    (P : Submodule K (MvPolynomial (σ ⊕ Fin n) K))
    (hP : ∀ a : Fin (counts j) × Fin (counts (R-j)),f a.1*g a.2∈P) :
    ∃ p : Space n d q J counts O,
      Function.Injective (ProductRows.multiplication counts (layers p) J R) ∧
      (ProductRows.multiplication counts (layers p) J R).range≤P := by
  obtain ⟨E,hE,he,hg'⟩ := ProductRows.exists_cross_assignment counts hj
    (fun k u => ∀ i,u i∈biformImage (O k) (Forms K n (d-k)))
    (fun k i => Submodule.zero_mem _) f g hf hg
  refine ⟨ofPolynomialFamilies 0 E (fun k _ => hE k),?_,?_⟩
  · rw [products_ofPolynomialFamilies]
    apply ProductRows.multiplication_single_cross_row counts J R j hj E honly
    simpa only [he,hg'] using hi
  · rw [products_ofPolynomialFamilies]
    apply ProductRows.multiplication_single_cross_row_range counts J R j hj E honly P
    simpa only [he,hg'] using hP

variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_small_cross_profile_parameter {a b v : ℕ}
    (ha : 0<a) (hb : 0<b) (hv : 0<v)
    (T : ℕ → Poly K (a+b) →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0)
    (hm₂ : counts 2≤((a+2-1).choose 2-finrank K X)*(v+(d-2)-1).choose (d-2))
    (hm₄ : counts 4≤(b+4-1).choose 4*(v+(d-4)-1).choose (d-4)) :
    ∃ p : Space (v+v) d q J counts (fun j => Forms K (a+b) j⊓(T j).ker),
      Function.Injective (ProductRows.multiplication counts (layers p) J 6) ∧
      ∀ z,(ProductRows.multiplication counts (layers p) J 6 z).IsWeightedHomogeneous
        (Sum.elim (fun _ : Fin (a+b) => 0) (ProductRows.halfWeight (balancedScalarHalf v))) (d-2) := by
  obtain ⟨f,g,hf,hg,hfw,hgw,hi⟩ := exists_unequal_constrained_cross_pair (j := 2) (l := 4) (s := d-2) (t := d-4)
    (r := counts 2) (u := counts 4) ha hb hv
    (T 2) (0 : Poly K (a+b) →ₗ[K] Fin 0 → K) hm₂ (by simpa using hm₄)
  have hg' : ∀ i,g i∈biformImage (Forms K (a+b) 4⊓(T 4).ker) (Forms K (v+v) (d-4)) := by
    simpa only [hT,LinearMap.ker_zero,inf_top_eq] using hg
  obtain ⟨p,hpi,hprange⟩ := exists_cross_row_profile_parameter (q := q) (d := d)
    (O := fun j => Forms K (a+b) j⊓(T j).ker) 6 2 (by omega)
    (ProductRows.sixth_row_only_second counts J hz) f g hf hg' hi
    (weightedHomogeneousSubmodule K
      (Sum.elim (fun _ : Fin (a+b) => 0) (ProductRows.halfWeight (balancedScalarHalf v))) (d-2))
    (fun z => by
      rw [mem_weightedHomogeneousSubmodule]
      simpa only [add_zero] using (hfw z.1).mul (hgw z.2))
  exact ⟨p,hpi,fun z => hprange (LinearMap.mem_range_self _ z)⟩

theorem exists_small_cross_empty_row_parameter {a b v : ℕ}
    (ha : 0<a) (hb : 0<b) (hv : 0<v)
    (T : ℕ → Poly K (a+b) →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0) (R : J) (hR : R.val=6)
    (hm₂ : counts 2≤((a+2-1).choose 2-finrank K X)*(v+(d-2)-1).choose (d-2))
    (hm₄ : counts 4≤(b+4-1).choose 4*(v+(d-4)-1).choose (d-4))
    (Q : Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d)
    (hQ : Function.Injective (ProjectedPrefix.multiplication
      (fun α => MonomialExpansion.partialDegree (balancedScalarHalf v) α≠d-2) Q (d-R.val))) :
    ∃ p : Space (v+v) d q J counts (fun j => Forms K (a+b) j⊓(T j).ker),
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
      (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range := by
  obtain ⟨p,hp,hw⟩ := exists_small_cross_profile_parameter (q := q) ha hb hv T hT hz hm₂ hm₄
  exact exists_empty_profile_row_parameter (fun _ _ => inf_le_left) R
    (hz R.val R.property (by omega) (by omega)) (balancedScalarHalf v) (d-2) p
    (by rw [hR]; exact hp) (by rw [hR]; exact hw) Q hQ

end Froberg.PreparedParameters
