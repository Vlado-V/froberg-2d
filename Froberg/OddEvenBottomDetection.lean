module

public import Froberg.OddEvenTargetExtension
public import Froberg.OddBackgroundBottomDetection

@[expose] public section

/-! The checked upper-target surjection excludes zero-bottom covectors
after adding the actual common even-generator family. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

@[simp] theorem oddEvenTargetExtensionEquiv_mk
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (v : biformParitySpace K h m (2*d) 1) :
    oddEvenTargetExtensionEquiv Q F G E
      ((oddEvenRelativeMap Q F G E).range.mkQ ((fullOddRelations Q F G).mkQ v))=
      (fullOddRelations (Fin.append Q E) F G).mkQ v := rfl

theorem odd_even_append_bottom_detects
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (hupper : Function.Surjective (upperTargetMap (backgroundEnumeratedForms (Fin.append Q E) F G)))
    (ell : (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) →ₗ[K] K)
    (hA : (oddEvenRelativeMap Q F G E).range≤ell.ker)
    (hbottom : ∀ v : biformParitySpace K h m (2*d) 1,
      v.val.IsWeightedHomogeneous (blockWeight h m) 1 →
        ell ((fullOddRelations Q F G).mkQ v)=0) : ell=0 := by
  let eb := (oddEvenRelativeMap Q F G E).range.liftQ ell hA
  let ee := oddEvenTargetExtensionEquiv Q F G E
  let el := eb.comp ee.symm.toLinearMap
  have hv (v : biformParitySpace K h m (2*d) 1) :
      el ((fullOddRelations (Fin.append Q E) F G).mkQ v)=
        ell ((fullOddRelations Q F G).mkQ v) := by
    change eb (ee.symm ((fullOddRelations (Fin.append Q E) F G).mkQ v))=_
    rw [←oddEvenTargetExtensionEquiv_mk Q F G E v]
    change eb (ee.symm (ee _))=_
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hz : el=0 := oddBackground_bottom_detects (Fin.append Q E) F G hupper el (by
    intro v hvw
    rw [hv]
    exact hbottom v hvw)
  apply LinearMap.ext
  intro z
  obtain ⟨v,rfl⟩ := (fullOddRelations Q F G).mkQ_surjective z
  rw [←hv,hz]
  rfl

end Froberg
