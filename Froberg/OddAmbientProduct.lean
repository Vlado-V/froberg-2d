module

public import Froberg.OddBackgroundProduct

@[expose] public section

/-! Scalar multiplication in the ambient odd quotient, before imposing
positive-even private coefficients. Its projection to the full odd
quotient is the literal full-background multiplication. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def tensorScalarParityProduct : (Forms K h 0 ⊗[K] Forms K m d) →ₗ[K]
    biformParitySpace K h m d 1 →ₗ[K] biformParitySpace K h m (2*d) 1 :=
  evenOddBiformProduct.comp (evenBiformEmbedding (Nat.zero_le d) (by decide))

theorem tensorScalarParityProduct_private_mem
    (G : Fin u → biformParitySpace K h m d 1)
    (p : Forms K h 0 ⊗[K] Forms K m d) (i : Fin u) :
    tensorScalarParityProduct p (G i)∈(privateScalarRelations G).range := by
  classical
  refine ⟨Pi.single i p,?_⟩
  apply Subtype.ext
  rw [privateScalarRelations,LinearMap.comp_apply,privateEvenCoefficientMap_val]
  change _=(sumBiformMap p)*(G i).val
  rw [Finset.sum_eq_single i]
  · change (G i).val*sumBiformMap ((Pi.single i p : Fin u → Forms K h 0 ⊗[K] Forms K m d) i)=_
    rw [Pi.single_eq_same]
    exact mul_comm _ _
  · intro j _ hji
    change (G j).val*sumBiformMap ((Pi.single i p : Fin u → Forms K h 0 ⊗[K] Forms K m d) j)=0
    rw [Pi.single_eq_of_ne hji,map_zero]
    simp
  · simp

theorem tensorScalarParityProduct_relations
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (p : Forms K h 0 ⊗[K] Forms K m d) :
    oddBackgroundCoefficientRelations F G ≤
      (ambientOddRelations Q F G).comap (tensorScalarParityProduct p) := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (show (privateEvenCoefficientMap F).range ≤ ambientOddRelations Q F G from
      le_trans le_sup_right le_sup_left)
      (evenOddBiformProduct_generator_mem F (evenBiformEmbedding (Nat.zero_le d) (by decide) p) i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (show (privateScalarRelations G).range ≤ ambientOddRelations Q F G from le_sup_right)
      (tensorScalarParityProduct_private_mem G p i)

def oddAmbientScalarProduct
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (Forms K h 0 ⊗[K] Forms K m d) →ₗ[K]
      (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) →ₗ[K]
        (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G) where
  toFun p := (oddBackgroundCoefficientRelations F G).liftQ
    ((ambientOddRelations Q F G).mkQ.comp (tensorScalarParityProduct p)) (by
      rw [LinearMap.ker_comp,Submodule.ker_mkQ]
      exact tensorScalarParityProduct_relations Q F G p)
  map_add' p p' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective x
    change (ambientOddRelations Q F G).mkQ (tensorScalarParityProduct (p+p') v)=
      (ambientOddRelations Q F G).mkQ (tensorScalarParityProduct p v)+
      (ambientOddRelations Q F G).mkQ (tensorScalarParityProduct p' v)
    rw [map_add,LinearMap.add_apply,map_add]
  map_smul' c p := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective x
    change (ambientOddRelations Q F G).mkQ (tensorScalarParityProduct (c • p) v)=
      c • (ambientOddRelations Q F G).mkQ (tensorScalarParityProduct p v)
    rw [map_smul,LinearMap.smul_apply,map_smul]

@[simp] theorem oddAmbientScalarProduct_mk
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (p : Forms K h 0 ⊗[K] Forms K m d) (v : biformParitySpace K h m d 1) :
    oddAmbientScalarProduct Q F G p ((oddBackgroundCoefficientRelations F G).mkQ v)=
      (ambientOddRelations Q F G).mkQ (tensorScalarParityProduct p v) := rfl


theorem ambientOddRelations_le_full
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    ambientOddRelations Q F G ≤ fullOddRelations Q F G := by
  apply sup_le_sup_left
  exact LinearMap.range_comp_le_range _ _

def oddAmbientToFull
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    (biformParitySpace K h m (2*d) 1 ⧸ ambientOddRelations Q F G) →ₗ[K]
      (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) :=
  Submodule.mapQ _ _ LinearMap.id (by
    simpa only [Submodule.comap_id] using ambientOddRelations_le_full Q F G)

@[simp] theorem oddAmbientToFull_mk
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (v : biformParitySpace K h m (2*d) 1) :
    oddAmbientToFull Q F G ((ambientOddRelations Q F G).mkQ v)=
      (fullOddRelations Q F G).mkQ v := rfl

theorem oddAmbientToFull_surjective
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    Function.Surjective (oddAmbientToFull Q F G) := by
  intro x
  obtain ⟨v,rfl⟩ := (fullOddRelations Q F G).mkQ_surjective x
  exact ⟨(ambientOddRelations Q F G).mkQ v,rfl⟩

theorem oddAmbientScalarProduct_toFull
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (p : Forms K h 0 ⊗[K] Forms K m d)
    (v : biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) :
    oddAmbientToFull Q F G (oddAmbientScalarProduct Q F G p v)=
      oddBackgroundQuotientProduct Q F G
        (evenBiformEmbedding (Nat.zero_le d) (by decide) p) v := by
  obtain ⟨a,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective v
  rfl

end Froberg
