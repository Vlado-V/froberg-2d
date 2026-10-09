module

public import Froberg.CoreBiform
public import Froberg.BiformTensorFamily
public import Froberg.WeightedTriangularProducts

@[expose] public section

/-! Literal polynomial row maps for deformed biform generators. Their top
components are the checked tensor multiplication maps, and all higher
components vanish. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] {ι : Type*} [Fintype ι]
variable {h m j e x y : ℕ}
attribute [local instance] tensorGroup

@[simp] theorem ambientBiform_tmul (u : Forms K h j) (v : Forms K m e) :
    ambientBiform (u ⊗ₜ[K] v) =
      rename (Fin.castAdd m) u.val * rename (Fin.natAdd h) v.val := by
  rw [ambientBiform_eq_split]
  simp only [LinearMap.comp_apply,TensorProduct.map_tmul,Submodule.subtype_apply,
    AlgEquiv.toLinearMap_apply,splitPolynomialEquiv_tmul]

theorem ambientBiform_weighted (g : Forms K h j ⊗[K] Forms K m e) :
    (ambientBiform g).IsWeightedHomogeneous (coreWeight h m) j := by
  have he : weightedHomogeneousComponent (coreWeight h m) j (ambientBiform g)=ambientBiform g := by
    change coreComponent h m j (ambientBiform g)=ambientBiform g
    rw [ambientBiform_eq_block,LinearMap.comp_apply,coreComponent_blockPolynomial,if_pos rfl]
  rw [←he]
  exact weightedHomogeneousComponent_isWeightedHomogeneous j _

/-- The tensor multiplication map is exactly ordinary multiplication after
embedding both biforms in the polynomial ring. -/
theorem ambientBiform_product (g : Forms K h j ⊗[K] Forms K m e)
    (c : Forms K h x ⊗[K] Forms K m y) :
    ambientBiform (biformProduct g c)=ambientBiform g*ambientBiform c := by
  induction g using TensorProduct.induction_on with
  | zero => simp
  | add g g' hg hg' => simp only [map_add,LinearMap.add_apply,hg,hg',add_mul]
  | tmul u v =>
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add,hc,hc',mul_add]
    | tmul a b =>
      rw [biformProduct_tmul,TensorProduct.map_tmul]
      simp only [ambientBiform_tmul]
      change rename (Fin.castAdd m) (u.val*a.val)*rename (Fin.natAdd h) (v.val*b.val)=_
      rw [map_mul,map_mul]
      ring

/-- The relation row formed from actual deformed generators and homogeneous
biform coefficients. -/
def preparedBiformRow (p : ι → Poly K (h+m)) :
    (ι → Forms K h x ⊗[K] Forms K m y) →ₗ[K] Poly K (h+m) where
  toFun c := ∑ i,p i*ambientBiform (c i)
  map_add' c c' := by simp only [Pi.add_apply,map_add,mul_add,Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply,map_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

@[simp] theorem preparedBiformRow_apply (p : ι → Poly K (h+m))
    (c : ι → Forms K h x ⊗[K] Forms K m y) :
    preparedBiformRow p c=∑ i,p i*ambientBiform (c i) := rfl

/-- The leading coefficient row of a lower deformation is its homogeneous
biform multiplication row. This is an identity of actual polynomials. -/
theorem preparedBiformRow_top (p : ι → Poly K (h+m))
    (g : ι → Forms K h j ⊗[K] Forms K m e)
    (hp : ∀ i,coreComponent h m j (p i)=ambientBiform (g i))
    (c : ι → Forms K h x ⊗[K] Forms K m y) :
    coreComponent h m (j+x) (preparedBiformRow p c)=
      ambientBiform (biformTensorFamilyMap g c) := by
  rw [preparedBiformRow_apply,map_sum,biformTensorFamilyMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ambientBiform_product]
  exact weighted_component_product_top (coreWeight h m) _ _ _ j x
    (hp i) (ambientBiform_weighted (c i))

/-- No product from the row has an X-degree above its designated target. -/
theorem preparedBiformRow_above (p : ι → Poly K (h+m))
    (hp : ∀ i k,j<k → coreComponent h m k (p i)=0)
    (c : ι → Forms K h x ⊗[K] Forms K m y) {t : ℕ} (ht : j+x<t) :
    coreComponent h m t (preparedBiformRow p c)=0 := by
  rw [preparedBiformRow_apply,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact weighted_component_product_above (coreWeight h m) _ _ j x t
    (hp i) (ambientBiform_weighted (c i)) ht

/-- Every top biform has a preimage under the deformed polynomial row once
the corresponding homogeneous tensor row is onto. -/
theorem preparedBiformRow_top_surjective (p : ι → Poly K (h+m))
    (g : ι → Forms K h j ⊗[K] Forms K m e)
    (hp : ∀ i,coreComponent h m j (p i)=ambientBiform (g i))
    (hg : Function.Surjective (biformTensorFamilyMap (x := x) (y := y) g))
    (v : Forms K h (j+x) ⊗[K] Forms K m (e+y)) :
    ∃ c : ι → Forms K h x ⊗[K] Forms K m y,
      coreComponent h m (j+x) (preparedBiformRow p c)=ambientBiform v := by
  obtain ⟨c,rfl⟩ := hg v
  exact ⟨c,preparedBiformRow_top p g hp c⟩

end Froberg
