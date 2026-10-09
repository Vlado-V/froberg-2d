module

public import Froberg.OddBackgroundProductCompatibility
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

/-! Adding even generators gives exactly their relative multiplication
image in the fixed odd source and target, with a canonical quotient
identification to the actual enlarged endpoint odd target. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u e : ℕ}

theorem evenScalarOddFamily_append_apply
    (Q : Fin q → biformParitySpace K h m d 0)
    (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin (q+e) → biformParitySpace K h m d 1) :
    evenScalarOddFamily (Fin.append Q E) a=
      evenScalarOddFamily Q (fun i => a (i.castAdd e))+
        evenScalarOddFamily E (fun i => a (i.natAdd q)) := by
  apply Subtype.ext
  simp only [evenScalarOddFamily,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,Submodule.coe_sum,Submodule.coe_add]
  change (∑ i,(Fin.append Q E i).val*(a i).val)=_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  rfl

theorem evenScalarOddFamily_append_range
    (Q : Fin q → biformParitySpace K h m d 0)
    (E : Fin e → biformParitySpace K h m d 0) :
    (evenScalarOddFamily (Fin.append Q E)).range=
      (evenScalarOddFamily Q).range ⊔ (evenScalarOddFamily E).range := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    rw [evenScalarOddFamily_append_apply]
    exact Submodule.add_mem_sup ⟨_,rfl⟩ ⟨_,rfl⟩
  · apply sup_le
    · rintro _ ⟨a,rfl⟩
      refine ⟨Fin.append a 0,?_⟩
      rw [evenScalarOddFamily_append_apply]
      simp only [Fin.append_left,Fin.append_right,map_zero,add_zero]
    · rintro _ ⟨a,rfl⟩
      refine ⟨Fin.append 0 a,?_⟩
      rw [evenScalarOddFamily_append_apply]
      simp only [Fin.append_left,Fin.append_right,map_zero,zero_add]

theorem fullOddRelations_append_even
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) :
    fullOddRelations (Fin.append Q E) F G=
      fullOddRelations Q F G ⊔ (evenScalarOddFamily E).range := by
  simp only [fullOddRelations,oddBackgroundRelations,evenScalarOddFamily_append_range]
  ac_rfl

def oddEvenRelativeMap
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) :
    (Fin e → biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) →ₗ[K]
      (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) :=
  ∑ i,(oddBackgroundQuotientProduct Q F G (E i)).comp (LinearMap.proj i)

@[simp] theorem oddEvenRelativeMap_apply
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddEvenRelativeMap Q F G E a=∑ i,oddBackgroundQuotientProduct Q F G (E i) (a i) := by
  simp only [oddEvenRelativeMap,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]

theorem oddEvenRelativeMap_add
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (B E : Fin e → biformParitySpace K h m d 0) :
    oddEvenRelativeMap Q F G (fun i => B i+E i)=
      oddEvenRelativeMap Q F G B+oddEvenRelativeMap Q F G E := by
  apply LinearMap.ext
  intro a
  simp only [oddEvenRelativeMap_apply,map_add,LinearMap.add_apply,Finset.sum_add_distrib]

theorem oddEvenRelativeMap_mk
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → biformParitySpace K h m d 1) :
    oddEvenRelativeMap Q F G E (fun i => (oddBackgroundCoefficientRelations F G).mkQ (a i))=
      (fullOddRelations Q F G).mkQ (evenScalarOddFamily E a) := by
  rw [oddEvenRelativeMap_apply]
  simp only [oddBackgroundQuotientProduct_mk,←map_sum]
  congr 1
  simp only [evenScalarOddFamily,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
  rfl

theorem oddEvenRelativeMap_range
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) :
    (oddEvenRelativeMap Q F G E).range=
      (evenScalarOddFamily E).range.map (fullOddRelations Q F G).mkQ := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    choose v hv using fun i => (oddBackgroundCoefficientRelations F G).mkQ_surjective (a i)
    have ha : a=fun i => (oddBackgroundCoefficientRelations F G).mkQ (v i) := by
      funext i
      exact (hv i).symm
    rw [ha,oddEvenRelativeMap_mk]
    exact ⟨_,⟨v,rfl⟩,rfl⟩
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨_,oddEvenRelativeMap_mk Q F G E a⟩

def oddEvenTargetExtensionEquiv
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) :
    ((biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) ⧸
      (oddEvenRelativeMap Q F G E).range) ≃ₗ[K]
    (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations (Fin.append Q E) F G) :=
  (Submodule.quotEquivOfEq _ _ (oddEvenRelativeMap_range Q F G E)).trans
    ((Submodule.quotientQuotientEquivQuotientSup _ _).trans
      (Submodule.quotEquivOfEq _ _ (fullOddRelations_append_even Q F G E).symm))

def oddEvenEndpointExtensionEquiv
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (E : Fin e → biformParitySpace K h m d 0) :
    ((biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) ⧸
      (oddEvenRelativeMap Q F G E).range) ≃ₗ[K]
      oddTargetSpace ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
        (backgroundEnumeratedForms (Fin.append Q E) F G) :=
  (oddEvenTargetExtensionEquiv Q F G E).trans (oddBackgroundEndpointEquiv (Fin.append Q E) F G)

end Froberg
