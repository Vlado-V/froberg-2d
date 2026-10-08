import Froberg.PreparedParameterMaps
import Froberg.BiformOutputConstraint

/-! Adjoining private scalar variables preserves the actual prepared
coefficient space and every generator, with no new choices of coefficients. -/
noncomputable section
namespace Froberg
open MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {a z e : ℕ}

theorem biformImage_core_extension
    (O : Submodule K (MvPolynomial σ K))
    {p : MvPolynomial (σ ⊕ Fin a) K}
    (hp : p∈biformImage O (Forms K a e)) :
    rename (Sum.map id (Fin.castAdd z)) p∈biformImage O (Forms K (a+z) e) := by
  rcases hp with ⟨v,⟨t,rfl⟩,rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    change rename (Sum.map id (Fin.castAdd z))
      (tensorEquivSum K σ (Fin a) K (x.val ⊗ₜ[K] y.val))∈_
    rw [tensorEquivSum_tmul,map_mul,rename_rename,rename_rename]
    have hh := mul_mem_biformImage O (Forms K (a+z) e) x.property
      (show rename (Fin.castAdd z) y.val∈Forms K (a+z) e from y.property.rename_isHomogeneous)
    simpa only [Function.comp_def,Sum.map_inl,Sum.map_inr,id_eq,rename_rename] using hh
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

namespace PreparedParameters
variable [Fintype σ] {d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

/-- Keep the same scalar and layer coefficients and adjoin z fresh variables. -/
def coreExtension (z : ℕ) : Space a d q J counts O →ₗ[K] Space (a+z) d q J counts O where
  toFun p :=
    ((fun i => ⟨rename (Fin.castAdd z) (p.1 i).val,(p.1 i).property.rename_isHomogeneous⟩),
      fun j i => ⟨rename (Sum.map id (Fin.castAdd z)) (p.2 j i).val,
        biformImage_core_extension (O j.val) (p.2 j i).property⟩)
  map_add' p r := by
    apply Prod.ext
    · funext i; apply Subtype.ext; exact map_add _ _ _
    · funext j i; apply Subtype.ext; exact map_add _ _ _
  map_smul' c p := by
    apply Prod.ext
    · funext i; apply Subtype.ext; exact map_smul (rename (Fin.castAdd z)).toLinearMap c _
    · funext j i; apply Subtype.ext
      exact map_smul (rename (Sum.map id (Fin.castAdd z))).toLinearMap c _

@[simp] theorem coreExtension_scalar (p : Space a d q J counts O) (i : Label q J counts) :
    scalar (coreExtension z p) i=rename (Sum.map id (Fin.castAdd z)) (scalar p i) := by
  simp only [scalar,coreExtension,LinearMap.coe_mk,AddHom.coe_mk,rename_rename]
  rfl

@[simp] theorem coreExtension_high (p : Space a d q J counts O) (i : Label q J counts) :
    high (coreExtension z p) i=rename (Sum.map id (Fin.castAdd z)) (high p i) := by
  cases i with
  | inl i => simp only [high_scalar_label,map_zero]
  | inr i => rfl

@[simp] theorem coreExtension_generator (p : Space a d q J counts O) (i : Label q J counts) :
    generator (coreExtension z p) i=
      rename (Sum.map id (Fin.castAdd z)) (generator p i) := by
  simp only [generator,coreExtension_scalar,coreExtension_high,map_add]

theorem coreExtension_injective : Function.Injective (coreExtension (a := a) (O := O)
    (d := d) (q := q) (J := J) (counts := counts) z) := by
  intro p r h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    apply rename_injective (Fin.castAdd z) (Fin.castAdd_injective a z)
    exact congrArg (fun x : Space (a+z) d q J counts O => (x.1 i).val) h
  · funext j i
    apply Subtype.ext
    apply rename_injective (Sum.map id (Fin.castAdd z))
      (Function.Injective.sumMap (fun _ _ h => h) (Fin.castAdd_injective a z))
    exact congrArg (fun x : Space (a+z) d q J counts O => (x.2 j i).val) h

end PreparedParameters
end Froberg
