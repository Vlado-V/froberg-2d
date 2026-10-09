module

public import Froberg.SingleLayerParameters
public import Froberg.BiformProductProfile

@[expose] public section

/-! The small quadratic product witness has both injective multiplication
and the scalar-profile support used to separate it from old scalar products. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem exists_single_layer_profile_parameter (j : ℕ)
    (hz : ∀ k∈J,k≠j → counts k=0)
    (f : Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (hf : ∀ i,f i∈biformImage (O j) (Forms K n (d-j)))
    (hi : LinearIndependent K (pairProducts f))
    (P : Submodule K (MvPolynomial (σ ⊕ Fin n) K))
    (hP : ∀ a,pairProducts f a∈P) :
    ∃ p : Space n d q J counts O,
      (∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R)) ∧
      ∀ R,(ProductRows.multiplication counts (layers p) J R).range≤P := by
  obtain ⟨E,hE,he⟩ := ProductRows.exists_diagonal_assignment counts j
    (fun k g => ∀ i,g i∈biformImage (O k) (Forms K n (d-k)))
    (fun k i => Submodule.zero_mem _) f hf
  refine ⟨ofPolynomialFamilies 0 E (fun k _ => hE k),?_,?_⟩
  · intro R
    rw [products_ofPolynomialFamilies]
    apply ProductRows.multiplication_single_layer counts J j hz
    rwa [he]
  · intro R
    rw [products_ofPolynomialFamilies]
    apply ProductRows.multiplication_single_layer_range counts J j hz E P
    rwa [he]

variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_strong_quartic_profile_parameter {h : ℕ}
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈J,k≠2 → counts k=0)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(S.card.choose 2/2)) :
    ∃ p : Space n 4 q J counts (fun j => Forms K h j⊓(T j).ker),
      (∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R)) ∧
      ∀ R a,(ProductRows.multiplication counts (layers p) J R a).IsWeightedHomogeneous
        (Sum.elim (fun _ : Fin h => 0) (ProductRows.halfWeight S)) 2 := by
  obtain ⟨C,f,hC,hprofile,hf,hi⟩ := strong_quadratic_paired_diagonal_exists (t := 2) (T 2) S hS hm
  obtain ⟨p,hpi,hprange⟩ := exists_single_layer_profile_parameter (q := q) (n := n) (d := 4)
    (J := J) (counts := counts) (O := fun j => Forms K h j⊓(T j).ker) 2 hz f
    (fun i => biformImage_mono le_rfl hC (hf i)) hi
    (weightedHomogeneousSubmodule K
      (Sum.elim (fun _ : Fin h => 0) (ProductRows.halfWeight S)) 2)
    (biform_pairProducts_single_profile S (Forms K h 2⊓(T 2).ker) C hprofile f hf)
  exact ⟨p,hpi,fun R a => hprange R (LinearMap.mem_range_self _ a)⟩

end Froberg.PreparedParameters
