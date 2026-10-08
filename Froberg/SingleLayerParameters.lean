import Froberg.SingleLayerProducts
import Froberg.StrongQuadraticDiagonal
import Froberg.PreparedProductOpen

/-! The strengthened small-degree diagonal witness is a point of the
same prepared parameter space used by the row openness argument. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem exists_single_layer_product_parameter (j : ℕ)
    (hz : ∀ k∈J,k≠j → counts k=0)
    (f : Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (hf : ∀ i,f i∈biformImage (O j) (Forms K n (d-j)))
    (hi : LinearIndependent K (pairProducts f)) :
    ∃ p : Space n d q J counts O,
      ∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  obtain ⟨E,hE,he⟩ := ProductRows.exists_diagonal_assignment counts j
    (fun k g => ∀ i,g i∈biformImage (O k) (Forms K n (d-k)))
    (fun k i => Submodule.zero_mem _) f hf
  refine ⟨ofPolynomialFamilies 0 E (fun k _ => hE k),?_⟩
  intro R
  rw [products_ofPolynomialFamilies]
  apply ProductRows.multiplication_single_layer counts J j hz
  rwa [he]

variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_strong_quadratic_product_parameter {h : ℕ}
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈J,k≠2 → counts k=0)
    (C : Submodule K (Poly K n)) [Module.Finite K C]
    (hC : C≤Forms K n (d-2))
    (hCi : Function.Injective (subspaceSymmetricMultiplication C))
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(finrank K C/2)) :
    ∃ p : Space n d q J counts (fun j => Forms K h j ⊓ (T j).ker),
      ∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  obtain ⟨f,hf,hi⟩ := strong_quadratic_diagonal_exists C hCi (T 2) hm
  apply exists_single_layer_product_parameter 2 hz f _ hi
  intro i
  exact biformImage_mono le_rfl hC (hf i)

theorem exists_strong_cubic_product_parameter {h : ℕ}
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈J,k≠2 → counts k=0)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(n/2)) :
    ∃ p : Space n 3 q J counts (fun j => Forms K h j ⊓ (T j).ker),
      ∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  obtain ⟨f,hf,hi⟩ := strong_quadratic_linear_diagonal_exists (T 2) hm
  exact exists_single_layer_product_parameter 2 hz f hf hi

theorem exists_strong_quartic_product_parameter {h : ℕ}
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈J,k≠2 → counts k=0)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(S.card.choose 2/2)) :
    ∃ p : Space n 4 q J counts (fun j => Forms K h j ⊓ (T j).ker),
      ∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  obtain ⟨C,f,hC,_,hf,hi⟩ := strong_quadratic_paired_diagonal_exists (T 2) S hS hm
  apply exists_single_layer_product_parameter 2 hz f _ hi
  intro i
  exact biformImage_mono le_rfl hC (hf i)

end Froberg.PreparedParameters
