module

public import Froberg.PrivateColumns
public import Froberg.CommonMultipleCount

@[expose] public section

/-! Only lower-order many discarded targets meet any regular source monomial. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset MonomialExpansion OuterInjection
variable {a z s b : ℕ}

def badTargets (ι : Fin b ↪ Fin z) : Finset (Degree (a+z) (2*s+1)) :=
  univ.filter (fun β => ∃ i, privateExponent a s ι i ≤ β.val)

lemma card_bad_regular_targets (hn : 0 < a+z) (ι : Fin b ↪ Fin z)
    (α : Degree (a+z) s) (hα : ∀ i, α.val ≠ privateExponent a s ι i) :
    ((badTargets (s := s) ι).filter (fun β => α.val ≤ β.val)).card ≤ b*(a+z+s-1).choose s := by
  classical
  let T := fun i : Fin b => (univ : Finset (Degree (a+z) (2*s+1))).filter
    (fun β => α.val ≤ β.val ∧ privateExponent a s ι i ≤ β.val)
  have hT (i : Fin b) : (T i).card ≤ (a+z+s-1).choose s := by
    have hi : Set.InjOn (fun β : Degree (a+z) (2*s+1) => β.val) (T i) := by
      intro x hx y hy he
      exact Subtype.ext he
    rw [← card_image_of_injOn hi]
    apply card_common_targets_le hn α.val (privateExponent a s ι i)
      (degree_val α) (privateExponent_degree ι i) (hα i)
    intro β hβ
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hβ
    exact ⟨degree_val γ,(mem_filter.mp hγ).2⟩
  have he : (badTargets (s := s) ι).filter (fun β => α.val ≤ β.val) = univ.biUnion T := by
    ext β
    simp only [badTargets,mem_filter,mem_univ,true_and,mem_biUnion,T]
    aesop
  rw [he]
  simpa only [card_univ,Fintype.card_fin] using
    card_biUnion_le_card_mul (univ : Finset (Fin b)) T ((a+z+s-1).choose s) (fun i _ => hT i)

end Froberg.PrivateColumns
