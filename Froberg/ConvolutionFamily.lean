module

public import Froberg.SymmetricConvolution
public import Froberg.VectorFormFamily

@[expose] public section

/-! The actual finite family of vector-valued forms supplied by convolution. -/
noncomputable section
namespace Froberg
open Finset TensorProduct
variable {K : Type*} [Field K]

/-- A subset product in any chosen number of variables. -/
def momentSubproduct {N e : ℕ} (n : ℕ) (t : Fin N → K)
    (I : {I : Finset (Fin N) // I.card = e}) : Forms K n e :=
  ⟨∏ i ∈ I.val, momentLinear n (t i), by
    change (∏ i ∈ I.val, momentLinear n (t i)).IsHomogeneous e
    simpa only [I.property] using moment_finset_homogeneous n t I.val⟩

theorem convolutionHom_momentProduct {a e m : ℕ}
    (t : Fin (m+a-1+e-1) → K) (I : ConvolutionSubset (m+a-1) e) :
    convolutionHom a m (momentProduct t I).val =
      (momentSubproduct (e := e) a t I).val ⊗ₜ[K] (momentSubproduct (e := e) m t I).val := by
  simp only [momentProduct, momentSubproduct, map_prod, convolutionHom_momentLinear]
  exact finset_prod_tmul I.val _ _

theorem convolutionFamily_single {a e m : ℕ}
    (t : Fin (m+a-1+e-1) → K) (I : ConvolutionSubset (m+a-1) e)
    (g : Forms K m (a-1)) :
    biformInclusion a m e (e+(a-1))
      (vectorFormFamilyMap (momentSubproduct (e := e) a t) (momentSubproduct (e := e) m t) (Pi.single I g)) =
      symmetricConvolutionMap a e m (momentProduct t I ⊗ₜ[K] g) := by
  classical
  rw [vectorFormFamilyMap_single, symmetricConvolutionMap_tmul,
    convolutionHom_momentProduct]
  change (momentSubproduct (e := e) a t I).val ⊗ₜ[K]
      ((momentSubproduct (e := e) m t I).val * g.val) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- For any sufficiently large distinct scalar tuple, the explicit product
family reaches every homogeneous vector-valued form of the target degree. -/
theorem convolutionFamily_surjective {a e m : ℕ} (ha : 0<a) (hm : 0<m)
    [Infinite K] (t : Fin (m+a-1+e-1) → K) (ht : Function.Injective t) :
    Function.Surjective (vectorFormFamilyMap (t := a-1)
      (momentSubproduct (e := e) a t) (momentSubproduct (e := e) m t)) := by
  classical
  let F := vectorFormFamilyMap (t := a-1) (momentSubproduct (e := e) a t) (momentSubproduct (e := e) m t)
  let J := biformInclusion (K := K) a m e (e+(a-1))
  let R := (J.comp F).range
  let B := momentProductsBasis (show 0 < m+a-1 by omega) t ht
  have hconv (x : Forms K (m+a-1) e ⊗[K] Forms K m (a-1)) :
      symmetricConvolutionMap a e m x ∈ R := by
    induction x using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using Submodule.zero_mem R
    | tmul f g =>
      let L : Forms K (m+a-1) e →ₗ[K] BiformAlgebra K a m :=
        (symmetricConvolutionMap a e m).comp
          ((TensorProduct.mk K (Forms K (m+a-1) e) (Forms K m (a-1))).flip g)
      have hB : Submodule.span K (Set.range B) ≤ R.comap L := by
        apply Submodule.span_le.mpr
        rintro x ⟨I, rfl⟩
        change symmetricConvolutionMap a e m (B I ⊗ₜ[K] g) ∈ R
        refine ⟨Pi.single I g, ?_⟩
        simpa only [J, F, LinearMap.comp_apply, B, momentProductsBasis_apply] using
          convolutionFamily_single t I g
      rw [B.span_eq] at hB
      exact hB (Submodule.mem_top : f ∈ (⊤ : Submodule K (Forms K (m+a-1) e)))
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem R hx hy
  intro z
  have hz : J z ∈ (symmetricConvolutionMap (K := K) a e m).range := by
    have h := biform_range_le_convolution_range (K := K) (e := e) ha hm
    rw [← show e+(a-1) = a+e-1 by omega] at h
    exact h ⟨z, rfl⟩
  obtain ⟨x, hx⟩ := hz
  have hr := hconv x
  rw [hx] at hr
  obtain ⟨g, hg⟩ := hr
  exact ⟨g, biformInclusion_injective a m e _ hg⟩

/-- Convolution supplies exactly `choose(m+a+e-2,e)` vector forms. -/
theorem exists_convolution_family [Infinite K] {a e m : ℕ} (ha : 0<a) (hm : 0<m) :
    ∃ (o : ConvolutionSubset (m+a-1) e → Forms K a e)
      (f : ConvolutionSubset (m+a-1) e → Forms K m e),
      Function.Surjective (vectorFormFamilyMap (t := a-1) o f) := by
  let t : Fin (m+a-1+e-1) → K := fun i => Infinite.natEmbedding K i.val
  have ht : Function.Injective t := (Infinite.natEmbedding K).injective.comp Fin.val_injective
  exact ⟨momentSubproduct (e := e) a t, momentSubproduct (e := e) m t, convolutionFamily_surjective ha hm t ht⟩

theorem convolution_family_card {a e m : ℕ} (ha : 0<a) (hm : 0<m) :
    Fintype.card (ConvolutionSubset (m+a-1) e) = (m+a+e-2).choose e := by
  rw [Fintype.card_finset_len, Fintype.card_fin]
  congr 1
  omega

end Froberg
