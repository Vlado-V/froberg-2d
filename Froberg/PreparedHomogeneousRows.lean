module

public import Froberg.BiformPreparedRows
public import Froberg.PolynomialTriangular

@[expose] public section

/-! Homogeneous codomain and ideal membership for the literal prepared
multiplication rows. These supply the rows used in polynomial elimination. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {ι : Type*} [Fintype ι]
variable {h m j e x y : ℕ}
attribute [local instance] tensorGroup

theorem preparedBiformRow_homogeneous {D : ℕ} (p : ι → Poly K (h+m))
    (hp : ∀ i,(p i).IsHomogeneous D)
    (c : ι → Forms K h x ⊗[K] Forms K m y) :
    (preparedBiformRow p c).IsHomogeneous (D+(x+y)) := by
  rw [preparedBiformRow_apply]
  apply IsHomogeneous.sum
  intro i _
  exact (hp i).mul (Quartic.SplitTensor.polynomialEmbedding (c i)).property

def preparedHomogeneousRow {D : ℕ} (p : ι → Poly K (h+m))
    (hp : ∀ i,(p i).IsHomogeneous D) :
    (ι → Forms K h x ⊗[K] Forms K m y) →ₗ[K] Forms K (h+m) (D+(x+y)) :=
  (preparedBiformRow p).codRestrict (Forms K (h+m) (D+(x+y)))
    (preparedBiformRow_homogeneous p hp)

@[simp] theorem preparedHomogeneousRow_val {D : ℕ} (p : ι → Poly K (h+m))
    (hp : ∀ i,(p i).IsHomogeneous D) (c : ι → Forms K h x ⊗[K] Forms K m y) :
    (preparedHomogeneousRow p hp c).val=preparedBiformRow p c := rfl

/-- A checked homogeneous tensor surjection gives the exact diagonal
surjection into the core-component subspace used by triangular elimination. -/
theorem preparedHomogeneousRow_top_surjective (p : ι → Poly K (h+m))
    (hp : ∀ i,(p i).IsHomogeneous (j+e))
    (g : ι → Forms K h j ⊗[K] Forms K m e)
    (htop : ∀ i,coreComponent h m j (p i)=ambientBiform (g i))
    (hg : Function.Surjective (biformTensorFamilyMap (x := x) (y := y) g))
    (v : coreCoefficientSpace K h m ((j+e)+(x+y)) (j+x)) :
    ∃ c : ι → Forms K h x ⊗[K] Forms K m y,
      coreComponent h m (j+x) (preparedHomogeneousRow p hp c).val=v.val := by
  let w : Poly K (h+m) := v.val
  have hv : w∈coreCoefficientSpace K h m ((j+e)+(x+y)) (j+x) := v.property
  rw [show (j+e)+(x+y)=(j+x)+(e+y) by omega,coreCoefficientSpace_eq_biform_range] at hv
  obtain ⟨u,hu⟩ := hv
  obtain ⟨c,hc⟩ := preparedBiformRow_top_surjective p g htop hg u
  exact ⟨c,hc.trans hu⟩

/-- Every deformed row is an actual product of its generators with
homogeneous coefficient forms. -/
theorem preparedBiformRow_mem_products (p : ι → Poly K (h+m))
    (c : ι → Forms K h x ⊗[K] Forms K m y) :
    preparedBiformRow p c ∈
      (Submodule.span K (Set.range p))*(Forms K (h+m) (x+y)) := by
  rw [preparedBiformRow_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.mul_mem_mul
  · exact Submodule.subset_span ⟨i,rfl⟩
  · exact (Quartic.SplitTensor.polynomialEmbedding (c i)).property

end Froberg
