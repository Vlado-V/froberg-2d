module

public import Froberg.PreparedCoreExtension

@[expose] public section

/-! Bijective output renaming on the complete prepared coefficient space. -/
noncomputable section
namespace Froberg
open MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*} {n e : ℕ}

theorem biformImage_output_rename (f : σ → τ)
    (O : Submodule K (MvPolynomial σ K))
    {p : MvPolynomial (σ ⊕ Fin n) K} (hp : p∈biformImage O (Forms K n e)) :
    rename (Sum.map f id) p∈biformImage (O.map (rename f).toLinearMap) (Forms K n e) := by
  have hh := biformImage_rename f (id : Fin n → Fin n) O (Forms K n e) ⟨p,hp,rfl⟩
  simpa only [rename_id,AlgHom.toLinearMap_id,Submodule.map_id,AlgHom.toLinearMap_apply] using hh

theorem biformImage_output_rename_eq (f : σ → τ)
    (O : Submodule K (MvPolynomial σ K)) :
    (biformImage O (Forms K n e)).map (rename (Sum.map f id)).toLinearMap=
      biformImage (O.map (rename f).toLinearMap) (Forms K n e) := by
  apply le_antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact biformImage_output_rename f O hp
  · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨a,ha,hea⟩ := x.property
      refine ⟨rename Sum.inl a*rename Sum.inr y.val,mul_mem_biformImage O _ ha y.property,?_⟩
      change rename (Sum.map f id) (rename Sum.inl a*rename Sum.inr y.val)=
        tensorEquivSum K τ (Fin n) K (x.val ⊗ₜ[K] y.val)
      rw [tensorEquivSum_tmul,map_mul,rename_rename,rename_rename]
      have ha' : rename f a=x.val := hea
      rw [←ha',rename_rename]
      rfl
    | add x y hx hy =>
      simpa only [map_add] using Submodule.add_mem _ hx hy

namespace PreparedParameters
variable [Fintype σ] [Fintype τ] {d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def outputRename (f : σ → τ) : Space n d q J counts O →ₗ[K]
    Space n d q J counts (fun j => (O j).map (rename f).toLinearMap) where
  toFun p := (p.1,fun j i => ⟨rename (Sum.map f id) (p.2 j i).val,
    biformImage_output_rename f _ (p.2 j i).property⟩)
  map_add' p r := by
    apply Prod.ext
    · rfl
    · funext j i; apply Subtype.ext; exact map_add _ _ _
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · funext j i; apply Subtype.ext
      exact map_smul (rename (Sum.map f id)).toLinearMap c _

@[simp] theorem outputRename_scalar (f : σ → τ) (p : Space n d q J counts O)
    (i : Label q J counts) :
    scalar (outputRename f p) i=rename (Sum.map f id) (scalar p i) := by
  simp only [scalar,outputRename,LinearMap.coe_mk,AddHom.coe_mk,rename_rename]
  rfl

@[simp] theorem outputRename_high (f : σ → τ) (p : Space n d q J counts O)
    (i : Label q J counts) :
    high (outputRename f p) i=rename (Sum.map f id) (high p i) := by
  cases i with
  | inl i => simp only [high_scalar_label,map_zero]
  | inr i => rfl

@[simp] theorem outputRename_generator (f : σ → τ) (p : Space n d q J counts O)
    (i : Label q J counts) :
    generator (outputRename f p) i=rename (Sum.map f id) (generator p i) := by
  simp only [generator,outputRename_scalar,outputRename_high,map_add]

theorem outputRename_surjective (f : σ → τ) :
    Function.Surjective (outputRename (n := n) (d := d) (q := q) (J := J) (counts := counts) (O := O) f) := by
  intro p
  have hp (j : J) (i : Fin (counts j.val)) :
      ∃ z : biformImage (O j.val) (Forms K n (d-j.val)),
        rename (Sum.map f id) z.val=(p.2 j i).val := by
    have hh := (biformImage_output_rename_eq (n := n) (e := d-j.val) f (O j.val)).ge (p.2 j i).property
    obtain ⟨z,hz,he⟩ := hh
    exact ⟨⟨z,hz⟩,he⟩
  choose z hz using hp
  refine ⟨(p.1,z),?_⟩
  apply Prod.ext
  · rfl
  · funext j i; exact Subtype.ext (hz j i)

theorem outputRename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective (outputRename (n := n) (d := d) (q := q) (J := J) (counts := counts) (O := O) f) := by
  intro p r he
  apply Prod.ext
  · exact congrArg (fun x : Space n d q J counts (fun j => (O j).map (rename f).toLinearMap) => x.1) he
  · funext j i
    apply Subtype.ext
    apply rename_injective (Sum.map f id) (Function.Injective.sumMap hf (fun _ _ h => h))
    exact congrArg (fun x : Space n d q J counts (fun j => (O j).map (rename f).toLinearMap) =>
      (x.2 j i).val) he

def outputRenameEquiv (f : σ ≃ τ) : Space n d q J counts O ≃ₗ[K]
    Space n d q J counts (fun j => (O j).map (rename f).toLinearMap) :=
  LinearEquiv.ofBijective (outputRename f) ⟨outputRename_injective f f.injective,outputRename_surjective f⟩

end PreparedParameters
end Froberg
