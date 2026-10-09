module

public import Froberg.BiformPolynomialOpen

@[expose] public section

/-! Full tensor-valued biform generator families, with polynomial rank opens.
Pure-tensor convolution witnesses are points of this full parameter space. -/
noncomputable section
namespace Froberg
open TensorProduct Module MvPolynomial
open Quartic
variable {K ι P : Type*} [Field K] [Fintype ι]
variable {h m j e x y : ℕ}

attribute [local instance] tensorGroup

/-- Literal multiplication in each tensor factor. -/
def biformProduct : (Forms K h j ⊗[K] Forms K m e) →ₗ[K]
    (Forms K h x ⊗[K] Forms K m y) →ₗ[K]
    Forms K h (j+x) ⊗[K] Forms K m (e+y) :=
  TensorProduct.map₂ gradedMultiplication gradedMultiplication

@[simp] theorem biformProduct_tmul (u : Forms K h j) (v : Forms K m e) :
    biformProduct (x := x) (y := y) (u ⊗ₜ[K] v) =
      TensorProduct.map (gradedMultiplication u) (gradedMultiplication v) := rfl

/-- The complete generator parameter space; each entry is any biform. -/
def biformTensorFamilyMap : (ι → Forms K h j ⊗[K] Forms K m e) →ₗ[K]
    (ι → Forms K h x ⊗[K] Forms K m y) →ₗ[K]
    Forms K h (j+x) ⊗[K] Forms K m (e+y) where
  toFun g := ∑ i, (biformProduct (g i)).comp (LinearMap.proj i)
  map_add' g g' := by
    ext c
    simp only [Pi.add_apply,map_add,LinearMap.add_comp,Finset.sum_add_distrib]
  map_smul' a g := by
    ext c
    simp only [Pi.smul_apply,map_smul,LinearMap.smul_comp,Finset.smul_sum,RingHom.id_apply]

@[simp] theorem biformTensorFamilyMap_apply
    (g : ι → Forms K h j ⊗[K] Forms K m e)
    (c : ι → Forms K h x ⊗[K] Forms K m y) :
    biformTensorFamilyMap g c = ∑ i, biformProduct (g i) (c i) := by
  simp [biformTensorFamilyMap]

@[simp] theorem biformTensorFamilyMap_pure (o : ι → Forms K h j) (f : ι → Forms K m e) :
    biformTensorFamilyMap (x := x) (y := y) (fun i => o i ⊗ₜ[K] f i) =
      biformFamilyMap o f := by
  ext c
  simp only [biformTensorFamilyMap_apply,biformProduct_tmul,biformFamilyMap_apply]

/-- A concrete convolution witness gives a rank certificate in the full tensor
family, so it can be intersected with other conditions on general biforms. -/
theorem biformTensorFamily_surjective_principal_open
    (g : (P → K) → ι → Forms K h j ⊗[K] Forms K m e)
    (hg : IsPolynomialFamily g) (a₀ : P → K)
    (ha₀ : Function.Surjective (biformTensorFamilyMap (x := x) (y := y) (g a₀))) :
    ∃ D : MvPolynomial P K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      Function.Surjective (biformTensorFamilyMap (x := x) (y := y) (g a)) := by
  obtain ⟨D,hD,hRank⟩ := rank_polynomial_principal_open
    (fun a => biformTensorFamilyMap (x := x) (y := y) (g a))
    (hg.linear_comp (biformTensorFamilyMap (x := x) (y := y))) a₀
  refine ⟨D,hD,fun a ha => ?_⟩
  have hr := hRank a ha
  rw [LinearMap.range_eq_top.mpr ha₀,finrank_top] at hr
  apply LinearMap.range_eq_top.mp
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hr)

end Froberg
