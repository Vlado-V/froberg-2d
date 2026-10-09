module

public import Froberg.IndexedPureTail
public import Froberg.PureCutoffPolynomial

@[expose] public section

/-! Finite admissibility of the pure family, without an eventual endpoint input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K]

def PureFamilyAdmissible {h d u : ℕ} (U : Fin u → Forms K h d) : Prop :=
  BilinearImage.image (gradedMultiplication (K := K) (n := h) (d := d) (e := 1)).flip
    (Submodule.span K (Set.range U))=⊤ ∧
  (¬Odd d → Submodule.span K (Set.range U)=⊤)

theorem pureFamilyAdmissible_of_span_top {h d u : ℕ} (U : Fin u → Forms K h d)
    (hU : Submodule.span K (Set.range U)=⊤) : PureFamilyAdmissible U := by
  refine ⟨?_,fun _ => hU⟩
  rw [hU]
  apply Submodule.map_injective_of_injective (f := (Forms K h (d+1)).subtype)
    (Submodule.injective_subtype _)
  rw [graded_flip_image_polynomial,Submodule.map_top,Submodule.range_subtype,
    Submodule.map_top,Submodule.range_subtype,forms_mul_forms]

theorem OddPureProjectionData.admissible {d h : ℕ} {hd : 1 ≤ d}
    (p : OddPureProjectionData K d h hd) (ho : Odd d) : PureFamilyAdmissible p.U :=
  ⟨p.cutoff,fun hn => False.elim (hn ho)⟩

end Froberg.PreparedTarget
