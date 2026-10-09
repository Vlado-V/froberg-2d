module

public import Froberg.BiformOutputRename
public import Froberg.PreparedParameters
public import Froberg.ProductRowRename

@[expose] public section

/-! Output reindexing sends actual prepared product witnesses to the common
chosen output coordinates, preserving their scalar profiles. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*} [Fintype σ] [Fintype τ]
variable {n d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {X : Type*} [AddCommGroup X] [Module K X]

def renameOutputParameter (e : σ ≃ τ) (T : ℕ → MvPolynomial τ K →ₗ[K] X)
    (p : Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓
      ((T j).comp (rename e).toLinearMap).ker)) :
    Space n d q J counts (fun j => homogeneousSubmodule τ K j⊓(T j).ker) :=
  (p.1,fun j i => ⟨rename (Sum.map e id) (p.2 j i).val,
    biform_output_rename_mem e (T j.val) (p.2 j i).property⟩)

theorem layers_renameOutputParameter (e : σ ≃ τ) (T : ℕ → MvPolynomial τ K →ₗ[K] X)
    (p : Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓
      ((T j).comp (rename e).toLinearMap).ker)) :
    layers (renameOutputParameter e T p) = fun j i => rename (Sum.map e id) (layers p j i) := by
  classical
  funext j i
  by_cases hj : j∈J
  · simp only [layers,dif_pos hj,renameOutputParameter]
  · simp only [layers,dif_neg hj,map_zero]

theorem products_renameOutputParameter (e : σ ≃ τ) (T : ℕ → MvPolynomial τ K →ₗ[K] X)
    (p : Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓
      ((T j).comp (rename e).toLinearMap).ker)) (R : ℕ) :
    ProductRows.multiplication counts (layers (renameOutputParameter e T p)) J R=
      (rename (Sum.map e id)).toLinearMap.comp (ProductRows.multiplication counts (layers p) J R) := by
  rw [layers_renameOutputParameter,ProductRows.multiplication_rename]

theorem renameOutputParameter_injective_products (e : σ ≃ τ)
    (T : ℕ → MvPolynomial τ K →ₗ[K] X)
    (p : Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓
      ((T j).comp (rename e).toLinearMap).ker)) {R : ℕ}
    (hp : Function.Injective (ProductRows.multiplication counts (layers p) J R)) :
    Function.Injective (ProductRows.multiplication counts (layers (renameOutputParameter e T p)) J R) := by
  rw [products_renameOutputParameter]
  exact (rename_injective _ (Sum.map_injective.mpr ⟨e.injective,Function.injective_id⟩)).comp hp

theorem renameOutputParameter_profile (e : σ ≃ τ) (T : ℕ → MvPolynomial τ K →ₗ[K] X)
    (p : Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓
      ((T j).comp (rename e).toLinearMap).ker)) {R k : ℕ} (S : Finset (Fin n))
    (hp : ∀ a,(ProductRows.multiplication counts (layers p) J R a).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) k) :
    ∀ a,(ProductRows.multiplication counts (layers (renameOutputParameter e T p)) J R a).IsWeightedHomogeneous
      (Sum.elim (fun _ : τ => 0) (ProductRows.halfWeight S)) k := by
  intro a
  rw [products_renameOutputParameter]
  exact biform_output_rename_profile e S (hp a)

end Froberg.PreparedParameters
