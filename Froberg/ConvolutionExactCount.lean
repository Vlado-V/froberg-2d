module

public import Froberg.ConvolutionDimension

@[expose] public section

/-! Extending the concrete convolution family to any prescribed larger count. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K W ι κ : Type*} [Field K] [AddCommMonoid W] [Module K W]
  [Fintype ι] [Fintype κ]

/-- Adding zero generators preserves the actual vector-form surjection. -/
theorem vectorFormFamily_surjective_extend {m e t : ℕ} (j : ι → κ)
    (hj : Function.Injective j) (o : ι → W) (f : ι → Forms K m e)
    (hF : Function.Surjective (vectorFormFamilyMap (t := t) o f)) :
    ∃ (O : κ → W) (F : κ → Forms K m e),
      (∀ i, O (j i) = o i) ∧ (∀ i, F (j i) = f i) ∧
      Function.Surjective (vectorFormFamilyMap (t := t) O F) := by
  let O := Function.extend j o (fun _ => 0)
  let F := Function.extend j f (fun _ => 0)
  have hO (i) : O (j i) = o i := hj.extend_apply o _ i
  have hscalar (i) : F (j i) = f i := hj.extend_apply f _ i
  refine ⟨O, F, hO, hscalar, ?_⟩
  intro z
  change z ∈ (vectorFormFamilyMap (t := t) O F).range
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul w g => exact vectorFormFamily_range_transfer LinearMap.id o f O F j hO hscalar hF w g
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- A count bound gives a tuple indexed by the requested `Fin r`, with literal
homogeneous vector forms and the required multiplication surjective. -/
theorem exists_convolution_family_of_count [Infinite K] [Module.Finite K W]
    {a e m r : ℕ} (ha : 0<a) (hm : 0<m)
    (hr : convolutionBlockCount (finrank K W) a e * (m+a+e-2).choose e ≤ r) :
    ∃ (o : Fin r → W) (f : Fin r → Forms K m e),
      Function.Surjective (vectorFormFamilyMap (t := a-1) o f) := by
  classical
  obtain ⟨o, f, hF⟩ := exists_rounded_convolution_family (K := K) (W := W) (e := e) ha hm
  have hcard : Fintype.card (Fin (convolutionBlockCount (finrank K W) a e) ×
      ConvolutionSubset (m+a-1) e) ≤ Fintype.card (Fin r) := by
    simpa only [convolution_blocks_card ha hm, Fintype.card_fin] using hr
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨O, F, hO, hscalar, hsurj⟩ := vectorFormFamily_surjective_extend j j.injective o f hF
  exact ⟨O, F, hsurj⟩

end Froberg
