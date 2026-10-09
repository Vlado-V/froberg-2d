module

public import Froberg.StrongQuarticDiagonal
public import Froberg.SingleDiagonalRow
public import Froberg.SingleLayerProfiles

@[expose] public section

/-! The stronger quartic output space gives a literal row-eight witness
in the common parameter space even when the quadratic layer is nonempty. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem exists_diagonal_row_profile_parameter (j : ℕ)
    (honly : ∀ r : ProductRows.Row J (2*j),ProductRows.Columns counts r → r.val.val=j)
    (f : Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (hf : ∀ i,f i∈biformImage (O j) (Forms K n (d-j)))
    (hi : LinearIndependent K (pairProducts f))
    (P : Submodule K (MvPolynomial (σ ⊕ Fin n) K))
    (hP : ∀ a,pairProducts f a∈P) :
    ∃ p : Space n d q J counts O,
      Function.Injective (ProductRows.multiplication counts (layers p) J (2*j)) ∧
      (ProductRows.multiplication counts (layers p) J (2*j)).range≤P := by
  obtain ⟨E,hE,he⟩ := ProductRows.exists_diagonal_assignment counts j
    (fun k g => ∀ i,g i∈biformImage (O k) (Forms K n (d-k)))
    (fun k i => Submodule.zero_mem _) f hf
  refine ⟨ofPolynomialFamilies 0 E (fun k _ => hE k),?_,?_⟩
  · rw [products_ofPolynomialFamilies]
    apply ProductRows.multiplication_single_diagonal_row counts J j E honly
    rwa [he]
  · rw [products_ofPolynomialFamilies]
    apply ProductRows.multiplication_single_diagonal_row_range counts J j E honly P
    rwa [he]

variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_strong_fourth_profile_parameter {h : ℕ}
    (hh : 144≤h) (hfour : 4∣h) (T : ℕ → Poly K h →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : counts 4≤(h^4/256)*(S.card.choose (d-4)/2)) :
    ∃ p : Space n d q J counts (fun j => Forms K h j⊓(T j).ker),
      Function.Injective (ProductRows.multiplication counts (layers p) J 8) ∧
      ∀ a,(ProductRows.multiplication counts (layers p) J 8 a).IsWeightedHomogeneous
        (Sum.elim (fun _ : Fin h => 0) (ProductRows.halfWeight S)) (2*((d-4)/2)) := by
  obtain ⟨C,f,hC,hprofile,hf,hi⟩ := strong_quartic_paired_diagonal_exists (K := K) hh hfour S hS hm
  have hf' : ∀ i,f i∈biformImage (Forms K h 4⊓(T 4).ker) (Forms K n (d-4)) := by
    rw [hT,LinearMap.ker_zero,inf_top_eq]
    exact fun i => biformImage_mono le_rfl hC (hf i)
  obtain ⟨p,hpi,hprange⟩ := exists_diagonal_row_profile_parameter (q := q) (n := n) (d := d)
    (J := J) (counts := counts) (O := fun j => Forms K h j⊓(T j).ker) 4
    (ProductRows.eighth_row_only_fourth counts J hz) f hf' hi
    (weightedHomogeneousSubmodule K
      (Sum.elim (fun _ : Fin h => 0) (ProductRows.halfWeight S)) (2*((d-4)/2)))
    (biform_pairProducts_single_profile S (Forms K h 4) C hprofile f hf)
  exact ⟨p,hpi,fun a => hprange (LinearMap.mem_range_self _ a)⟩

end Froberg.PreparedParameters
