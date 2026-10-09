module

public import Froberg.PreparedBiformCoordinates
public import Froberg.BiformProductProfile

@[expose] public section

/-! Output-variable equivalences preserve both prescribed biform spaces and
scalar half-degree profiles. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*} {n j s : ℕ}
variable {X : Type*} [AddCommGroup X] [Module K X]

theorem biformImage_mono_types
    {A : Type*} {B : Type*} {O O' : Submodule K (MvPolynomial A K)}
    {C C' : Submodule K (MvPolynomial B K)} (hO : O≤O') (hC : C≤C') :
    biformImage O C≤biformImage O' C' := by
  rintro _ ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change tensorEquivSum K A B K (a.val ⊗ₜ[K] b.val)∈_
    rw [tensorEquivSum_tmul]
    exact mul_mem_biformImage _ _ (hO a.property) (hC b.property)
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

theorem biform_output_rename_mem (e : σ ≃ τ)
    (T : MvPolynomial τ K →ₗ[K] X)
    {f : MvPolynomial (σ ⊕ Fin n) K}
    (hf : f∈biformImage
      (homogeneousSubmodule σ K j⊓(T.comp (rename e).toLinearMap).ker) (Forms K n s)) :
    rename (Sum.map e id) f∈biformImage
      (homogeneousSubmodule τ K j⊓T.ker) (Forms K n s) := by
  have h := biformImage_rename e id
    (homogeneousSubmodule σ K j⊓(T.comp (rename e).toLinearMap).ker)
    (Forms K n s) ⟨f,hf,rfl⟩
  apply biformImage_mono_types ?_ ?_ h
  · rintro z ⟨p,hp,rfl⟩
    exact ⟨hp.1.rename_isHomogeneous,hp.2⟩
  · rintro z ⟨p,hp,rfl⟩
    exact hp.rename_isHomogeneous

theorem biform_output_rename_profile (e : σ ≃ τ) (S : Finset (Fin n))
    {f : MvPolynomial (σ ⊕ Fin n) K}
    (hf : f.IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) j) :
    (rename (Sum.map e id) f).IsWeightedHomogeneous
      (Sum.elim (fun _ : τ => 0) (ProductRows.halfWeight S)) j := by
  apply rename_weightedHomogeneous
    (⟨Sum.map e id,Sum.map_injective.mpr ⟨e.injective,Function.injective_id⟩⟩ :
      (σ ⊕ Fin n) ↪ (τ ⊕ Fin n))
    (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight S)) _ _ hf
  rintro (x|y) <;> rfl

end Froberg
