import Froberg.MixedScalarComponents
import Froberg.OddBackgroundProduct

/-! Scalar coefficients already in the Q span give actual Q relations,
including when they multiply mixed private generators. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q u : ℕ}

private theorem scalarOddProduct_val (a : biformParitySpace K h m d 0)
    (b : biformParitySpace K h m d 1) :
    (evenScalarOddProduct a b).val=a.val*b.val := rfl

private theorem oddScalarProduct_val (a : biformParitySpace K h m d 1)
    (b : biformParitySpace K h m d 0) :
    (oddPrivateProduct a b).val=a.val*b.val := rfl

theorem scalar_span_private_product_mem
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (g : biformParitySpace K h m d 1)
    (v : Forms K h 0 ⊗[K] Forms K m d)
    (hv : v∈Submodule.span K (Set.range Q)) :
    oddPrivateProduct g (evenBiformEmbedding (Nat.zero_le d) (by decide) v)∈
      (evenScalarOddFamily (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))).range := by
  classical
  let L := (oddPrivateProduct g).comp
    (evenBiformEmbedding (K := K) (h := h) (m := m) (Nat.zero_le d) (by decide))
  have hs : Submodule.span K (Set.range Q)≤
      (evenScalarOddFamily (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))).range.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    refine ⟨Pi.single j g,?_⟩
    apply Subtype.ext
    simp only [evenScalarOddFamily,LinearMap.sum_apply,LinearMap.comp_apply,
      LinearMap.proj_apply,Submodule.coe_sum,L,scalarOddProduct_val,oddScalarProduct_val,
      evenBiformEmbedding_val,LinearMap.comp_apply]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
      exact mul_comm _ _
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij]
      simp
    · simp
  exact hs hv

theorem privateScalarRelations_mem_scalar_background
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (G : Fin u → biformParitySpace K h m d 1)
    (v : Fin u → Forms K h 0 ⊗[K] Forms K m d)
    (hv : ∀ i,v i∈Submodule.span K (Set.range Q)) :
    privateScalarRelations G v∈
      (evenScalarOddFamily (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))).range := by
  have he : privateScalarRelations G v=
      ∑ i,oddPrivateProduct (G i) (evenBiformEmbedding (Nat.zero_le d) (by decide) (v i)) := by
    apply Subtype.ext
    rw [privateScalarRelations_val,Submodule.coe_sum]
    rfl
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => scalar_span_private_product_mem Q (G i) (v i) (hv i))

theorem scalarBiform_span_iff (Q : Fin q → Forms K m d)
    (v : Forms K h 0 ⊗[K] Forms K m d) :
    v∈Submodule.span K (Set.range (fun i => scalarBiformEquiv (h := h) (Q i))) ↔
      (scalarBiformEquiv (h := h)).symm v∈Submodule.span K (Set.range Q) := by
  rw [Set.range_comp']
  change v∈Submodule.span K ((scalarBiformEquiv (K := K) (h := h) (n := m) (d := d)).toLinearMap '' Set.range Q) ↔ _
  rw [←Submodule.map_span]
  constructor
  · rintro ⟨a,ha,rfl⟩
    change (scalarBiformEquiv (K := K) (h := h) (n := m) (d := d)).symm
      (scalarBiformEquiv (h := h) a)∈Submodule.span K (Set.range Q)
    rw [LinearEquiv.symm_apply_apply]
    exact ha
  · intro hv
    exact ⟨(scalarBiformEquiv (h := h)).symm v,hv,LinearEquiv.apply_symm_apply _ _⟩

end Froberg
