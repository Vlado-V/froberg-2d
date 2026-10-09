module

public import Froberg.OddBackgroundSource
public import Froberg.ScalarBiformParameter

@[expose] public section

/-! Literal multiplication on the odd source and target background
quotients. Scalar multiplication is its restriction to pure Y forms. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def evenOddBiformProduct : biformParitySpace K h m d 0 →ₗ[K]
    biformParitySpace K h m d 1 →ₗ[K] biformParitySpace K h m (2*d) 1 where
  toFun := evenScalarOddProduct
  map_add' p p' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact add_mul _ _ _
  map_smul' c p := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact smul_mul_assoc c p.val v.val

theorem evenOddBiformProduct_generator_mem
    (F : Fin f → biformParitySpace K h m d 1)
    (p : biformParitySpace K h m d 0) (i : Fin f) :
    evenOddBiformProduct p (F i)∈(privateEvenCoefficientMap F).range := by
  classical
  refine ⟨Pi.single i p,?_⟩
  apply Subtype.ext
  rw [privateEvenCoefficientMap_val]
  change _=p.val*(F i).val
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    exact mul_comm _ _
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · simp

def oddBackgroundCoefficientRelations
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) :=
  Submodule.span K (Set.range F) ⊔ Submodule.span K (Set.range G)

theorem oddBackgroundProduct_relations
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (p : biformParitySpace K h m d 0) :
    oddBackgroundCoefficientRelations F G≤
      (fullOddRelations Q F G).comap (evenOddBiformProduct p) := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (show (privateEvenCoefficientMap F).range ≤ fullOddRelations Q F G from
      le_trans le_sup_right le_sup_left) (evenOddBiformProduct_generator_mem F p i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (show (privateEvenCoefficientMap G).range ≤ fullOddRelations Q F G from
      le_sup_right) (evenOddBiformProduct_generator_mem G p i)

def oddBackgroundQuotientProduct
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    biformParitySpace K h m d 0 →ₗ[K]
      (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) →ₗ[K]
        (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) where
  toFun p := (oddBackgroundCoefficientRelations F G).liftQ
    ((fullOddRelations Q F G).mkQ.comp (evenOddBiformProduct p)) (by
      rw [LinearMap.ker_comp,Submodule.ker_mkQ]
      exact oddBackgroundProduct_relations Q F G p)
  map_add' p p' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective x
    change (fullOddRelations Q F G).mkQ (evenOddBiformProduct (p+p') v)=
      (fullOddRelations Q F G).mkQ (evenOddBiformProduct p v)+
      (fullOddRelations Q F G).mkQ (evenOddBiformProduct p' v)
    rw [map_add,LinearMap.add_apply,map_add]
  map_smul' c p := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := (oddBackgroundCoefficientRelations F G).mkQ_surjective x
    change (fullOddRelations Q F G).mkQ (evenOddBiformProduct (c • p) v)=
      c • (fullOddRelations Q F G).mkQ (evenOddBiformProduct p v)
    rw [map_smul,LinearMap.smul_apply,map_smul]

@[simp] theorem oddBackgroundQuotientProduct_mk
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1)
    (p : biformParitySpace K h m d 0) (v : biformParitySpace K h m d 1) :
    oddBackgroundQuotientProduct Q F G p ((oddBackgroundCoefficientRelations F G).mkQ v)=
      (fullOddRelations Q F G).mkQ (evenOddBiformProduct p v) := rfl

def scalarEvenBiform : Forms K m d →ₗ[K] biformParitySpace K h m d 0 :=
  (evenBiformEmbedding (t := 0) (Nat.zero_le d) (by omega)).comp
    (scalarBiformEquiv (h := h)).toLinearMap

@[simp] theorem scalarEvenBiform_val (p : Forms K m d) :
    (scalarEvenBiform (h := h) p).val=rename Sum.inr p.val := by
  change sumBiformMap (scalarBiformEquiv (h := h) p)=_
  rw [scalarBiformEquiv_apply,sumBiformMap_tmul]
  change rename Sum.inl (1 : MvPolynomial (Fin h) K)*rename Sum.inr p.val=_
  rw [map_one,one_mul]

def oddBackgroundScalarProduct
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    Forms K m d →ₗ[K]
      (biformParitySpace K h m d 1 ⧸ oddBackgroundCoefficientRelations F G) →ₗ[K]
        (biformParitySpace K h m (2*d) 1 ⧸ fullOddRelations Q F G) :=
  (oddBackgroundQuotientProduct Q F G).comp scalarEvenBiform

end Froberg
