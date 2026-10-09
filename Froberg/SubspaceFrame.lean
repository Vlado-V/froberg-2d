module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! A subspace of prescribed dimension as a full-rank frame, with explicit
coordinates for every finite family in that subspace. -/
noncomputable section
namespace Froberg
open Module
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {H r : ℕ}

theorem exists_subspace_frame (W : Submodule K E) (hW : finrank K W=H)
    (o : Fin r → W) :
    ∃ (frame : Fin H → E) (c : Fin r → Fin H → K),
      LinearIndependent K frame ∧ Submodule.span K (Set.range frame)=W ∧
        ∀ i, (∑ a,c i a • frame a)=(o i).val := by
  classical
  subst H
  let b := Module.finBasis K W
  let frame : Fin (finrank K W) → E := fun a => (b a).val
  let c : Fin r → Fin (finrank K W) → K := fun i => b.equivFun (o i)
  have hf : LinearIndependent K frame := b.linearIndependent.map' W.subtype
    (LinearMap.ker_eq_bot.mpr W.subtype_injective)
  refine ⟨frame,c,hf,?_,?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact (b a).property
    · intro x hx
      have he : (∑ a,b.equivFun (⟨x,hx⟩ : W) a • frame a)=x := by
        have hh := congrArg Subtype.val (b.equivFun_symm_apply (b.equivFun (⟨x,hx⟩ : W)))
        simpa only [LinearEquiv.symm_apply_apply,Submodule.coe_sum,Submodule.coe_smul,frame] using hh.symm
      rw [←he]
      exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩))
  · intro i
    have hh := congrArg Subtype.val (b.equivFun_symm_apply (b.equivFun (o i)))
    simpa only [LinearEquiv.symm_apply_apply,Submodule.coe_sum,Submodule.coe_smul,frame,c] using hh.symm

end Froberg
