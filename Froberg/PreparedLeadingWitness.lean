import Froberg.PreparedPositiveLeadingOpen
import Froberg.PreparedParameterMaps

/-! Row witnesses provide precisely the leading independence needed for
the scalar-quotient condition in the final comparison. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {m d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem intrinsicLayer_independent_iff
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (p : Space m d q J counts O) (j : J) :
    LinearIndependent K (fun i => intrinsicLayerMap hO j i p) ↔
      LinearIndependent K (p.2 j) := by
  have heq (i : Fin (counts j.val)) : (intrinsicLayerMap hO j i p).val=(p.2 j i).val := by
    change layerMap j.val i p=(p.2 j i).val
    rw [layerMap_apply,layers,dif_pos j.property]
  constructor
  · intro hi
    apply LinearIndependent.of_comp (biformImage (O j.val) (Forms K m (d-j.val))).subtype
    have hh := hi.map' (FullBiform K σ m j.val (d-j.val)).subtype (Submodule.ker_subtype _)
    simpa only [Function.comp_def,Submodule.subtype_apply,heq] using hh
  · intro hi
    apply LinearIndependent.of_comp (FullBiform K σ m j.val (d-j.val)).subtype
    have hh := hi.map' (biformImage (O j.val) (Forms K m (d-j.val))).subtype (Submodule.ker_subtype _)
    simpa only [Function.comp_def,Submodule.subtype_apply,heq] using hh

theorem leading_witnesses_of_intrinsic
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hw : ∀ j : J,∃ p : Space m d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO j i p)) :
    ∀ j : J,∃ p : Space m d q J counts O,LinearIndependent K (p.2 j) := by
  intro j
  obtain ⟨p,hp⟩ := hw j
  exact ⟨p,(intrinsicLayer_independent_iff hO p j).mp hp⟩

end Froberg.PreparedParameters
