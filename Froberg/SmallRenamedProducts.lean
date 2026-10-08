import Froberg.SmallCrossParameters
import Froberg.PreparedProductOutputRename

/-! The exceptional small-degree product rows in any fixed finite output
coordinates. All witnesses remain points of the same prepared space. -/
noncomputable section
set_option maxHeartbeats 1400000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem exists_small_cross_profile_parameter_equiv {a b v : ℕ}
    (e : Fin (a+b) ≃ σ) (ha : 0<a) (hb : 0<b) (hv : 0<v)
    (T : ℕ → MvPolynomial σ K →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0)
    (hm₂ : counts 2≤((a+2-1).choose 2-finrank K X)*(v+(d-2)-1).choose (d-2))
    (hm₄ : counts 4≤(b+4-1).choose 4*(v+(d-4)-1).choose (d-4)) :
    ∃ p : Space (v+v) d q J counts (fun j => homogeneousSubmodule σ K j⊓(T j).ker),
      Function.Injective (ProductRows.multiplication counts (layers p) J 6) ∧
      ∀ z,(ProductRows.multiplication counts (layers p) J 6 z).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight (balancedScalarHalf v))) (d-2) := by
  let T' := fun j => (T j).comp (rename e).toLinearMap
  have hT' : T' 4=0 := by simp only [T',hT,LinearMap.zero_comp]
  obtain ⟨p,hp,hw⟩ := exists_small_cross_profile_parameter (q := q) ha hb hv T' hT' hz hm₂ hm₄
  exact ⟨renameOutputParameter e T p,renameOutputParameter_injective_products e T p hp,
    renameOutputParameter_profile e T p _ hw⟩

theorem exists_strong_fourth_profile_parameter_equiv {h : ℕ}
    (e : Fin h ≃ σ) (hh : 144≤h) (hfour : 4∣h)
    (T : ℕ → MvPolynomial σ K →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : counts 4≤(h^4/256)*(S.card.choose (d-4)/2)) :
    ∃ p : Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓(T j).ker),
      Function.Injective (ProductRows.multiplication counts (layers p) J 8) ∧
      ∀ a,(ProductRows.multiplication counts (layers p) J 8 a).IsWeightedHomogeneous
        (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) (2*((d-4)/2)) := by
  let T' := fun j => (T j).comp (rename e).toLinearMap
  have hT' : T' 4=0 := by simp only [T',hT,LinearMap.zero_comp]
  obtain ⟨p,hp,hw⟩ := exists_strong_fourth_profile_parameter (q := q) hh hfour T' hT' hz S hS hm
  exact ⟨renameOutputParameter e T p,renameOutputParameter_injective_products e T p hp,
    renameOutputParameter_profile e T p _ hw⟩

theorem exists_quintic_fourth_product_parameter {h : ℕ}
    (hh : 144≤h) (hfour : 4∣h) (T : ℕ → Poly K h →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0)
    (hm : counts 4≤(h^4/256)*(n/2)) :
    ∃ p : Space n 5 q J counts (fun j => Forms K h j⊓(T j).ker),
      Function.Injective (ProductRows.multiplication counts (layers p) J 8) := by
  obtain ⟨f,hf,hi⟩ := strong_quartic_linear_diagonal_exists (K := K) hh hfour hm
  have hf' : ∀ i,f i∈biformImage (Forms K h 4⊓(T 4).ker) (Forms K n (5-4)) := by
    simpa only [hT,LinearMap.ker_zero,inf_top_eq] using hf
  obtain ⟨p,hp,_⟩ := exists_diagonal_row_profile_parameter (q := q) (d := 5)
    (O := fun j => Forms K h j⊓(T j).ker) 4
    (ProductRows.eighth_row_only_fourth counts J hz) f hf' hi ⊤ (fun _ => Submodule.mem_top)
  exact ⟨p,hp⟩

theorem exists_quintic_fourth_product_parameter_equiv {h : ℕ}
    (e : Fin h ≃ σ) (hh : 144≤h) (hfour : 4∣h)
    (T : ℕ → MvPolynomial σ K →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈J,k≠2 → k≠4 → counts k=0)
    (hm : counts 4≤(h^4/256)*(n/2)) :
    ∃ p : Space n 5 q J counts (fun j => homogeneousSubmodule σ K j⊓(T j).ker),
      Function.Injective (ProductRows.multiplication counts (layers p) J 8) := by
  let T' := fun j => (T j).comp (rename e).toLinearMap
  have hT' : T' 4=0 := by simp only [T',hT,LinearMap.zero_comp]
  obtain ⟨p,hp⟩ := exists_quintic_fourth_product_parameter (q := q) hh hfour T' hT' hz hm
  exact ⟨renameOutputParameter e T p,renameOutputParameter_injective_products e T p hp⟩

theorem exists_strong_cubic_product_parameter_equiv {h : ℕ}
    (e : Fin h ≃ σ) (T : ℕ → MvPolynomial σ K →ₗ[K] X)
    (hz : ∀ k∈J,k≠2 → counts k=0)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(n/2)) :
    ∃ p : Space n 3 q J counts (fun j => homogeneousSubmodule σ K j⊓(T j).ker),
      ∀ R,Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  let T' := fun j => (T j).comp (rename e).toLinearMap
  obtain ⟨p,hp⟩ := exists_strong_cubic_product_parameter (q := q) T' hz hm
  exact ⟨renameOutputParameter e T p,fun R => renameOutputParameter_injective_products e T p (hp R)⟩

end Froberg.PreparedParameters
