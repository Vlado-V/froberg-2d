module

public import Froberg.BiformOutputConstraint
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-! Coefficientwise output constraints recover the exact constrained biform
space, rather than only a containing kernel. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ X : Type*} [AddCommGroup X] [Module K X]

/-- A biform killed by an output detector has every output coefficient in
that detector's kernel. -/
theorem mem_biformImage_inf_kernel
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    (T : MvPolynomial σ K →ₗ[K] X) {f : MvPolynomial (σ ⊕ τ) K}
    (hf : f∈biformImage O C) (hT : biformOutputMap T f=0) :
    f∈biformImage (O ⊓ T.ker) C := by
  rcases hf with ⟨a,⟨z,rfl⟩,rfl⟩
  let t : O →ₗ[K] X := T.comp O.subtype
  have hz0 : TensorProduct.map T LinearMap.id
      (TensorProduct.map O.subtype C.subtype z)=0 := by
    simpa only [biformOutputMap,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
      AlgEquiv.symm_apply_apply] using hT
  have hcomm : ∀ z : O ⊗[K] C,
      TensorProduct.map (LinearMap.id : X →ₗ[K] X) C.subtype (t.rTensor C z)=
      TensorProduct.map T LinearMap.id (TensorProduct.map O.subtype C.subtype z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  have hz : t.rTensor C z=0 := by
    apply TensorProduct.map_injective_of_flat_flat (LinearMap.id : X →ₗ[K] X) C.subtype
      Function.injective_id C.injective_subtype
    rw [hcomm,map_zero,hz0]
  have hbase : Function.Exact (t.ker.subtype : ↥t.ker →ₗ[K] ↥O) t :=
    LinearMap.exact_subtype_ker_map t
  have hex := Module.Flat.rTensor_exact (R := K) (↥C)
    (N := ↥t.ker) (N' := ↥O) (N'' := X)
    (f := (t.ker.subtype : ↥t.ker →ₗ[K] ↥O)) (g := t) hbase
  obtain ⟨u,hu⟩ := (hex z).mp hz
  let L : ↥t.ker →ₗ[K] ↥(O ⊓ T.ker) :=
    { toFun := fun x => ⟨x.val.val,⟨x.val.property,x.property⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨TensorProduct.map (O ⊓ T.ker).subtype C.subtype (TensorProduct.map L LinearMap.id u),
    ⟨TensorProduct.map L LinearMap.id u,rfl⟩,?_⟩
  apply congrArg (tensorEquivSum K σ τ K)
  rw [← hu]
  clear hu
  induction u using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Exact constrained-output membership is the intersection of the biform
space with the detector kernel. -/
theorem biformImage_inf_kernel
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    (T : MvPolynomial σ K →ₗ[K] X) :
    biformImage (O ⊓ T.ker) C=biformImage O C ⊓ (biformOutputMap T).ker := by
  apply le_antisymm
  · intro f hf
    constructor
    · rcases hf with ⟨a,⟨z,rfl⟩,rfl⟩
      let L : ↥(O ⊓ T.ker) →ₗ[K] ↥O := Submodule.inclusion inf_le_left
      refine ⟨TensorProduct.map O.subtype C.subtype (TensorProduct.map L LinearMap.id z),
        ⟨TensorProduct.map L LinearMap.id z,rfl⟩,?_⟩
      apply congrArg (tensorEquivSum K σ τ K)
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add,hx,hy]
    · exact biformImage_le_output_kernel T (O ⊓ T.ker) C inf_le_right hf
  · intro f hf
    exact mem_biformImage_inf_kernel O C T hf.1 hf.2

end Froberg
