module

public import Froberg.OddPrivateRelations

@[expose] public section

/-! The C.15 ambient and full odd quotients, with the actual Q, F, U+P
product maps and all positive even coefficient relations. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def evenScalarOddProduct (g : biformParitySpace K h m d 0) :
    biformParitySpace K h m d 1 →ₗ[K] biformParitySpace K h m (2*d) 1 where
  toFun v := ⟨g.val*v.val,by
    refine ⟨?_,?_⟩
    · change (g.val*v.val).IsHomogeneous (2*d)
      simpa only [two_mul] using g.property.1.mul v.property.1
    · change (g.val*v.val).IsWeightedHomogeneous (fun i => (blockWeight h m i : ZMod 2)) 1
      simpa only [zero_add] using g.property.2.mul v.property.2⟩
  map_add' v w := Subtype.ext (mul_add _ _ _)
  map_smul' a v := Subtype.ext (mul_smul_comm _ _ _)

def evenScalarOddFamily (Q : Fin q → biformParitySpace K h m d 0) :
    (Fin q → biformParitySpace K h m d 1) →ₗ[K] biformParitySpace K h m (2*d) 1 :=
  ∑ i,(evenScalarOddProduct (Q i)).comp (LinearMap.proj i)

def oddBackgroundRelations (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) : Submodule K (biformParitySpace K h m (2*d) 1) :=
  (evenScalarOddFamily Q).range ⊔ (privateEvenCoefficientMap F).range

def ambientOddRelations (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :=
  oddBackgroundRelations Q F ⊔ (privateScalarRelations G).range

def fullOddRelations (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :=
  oddBackgroundRelations Q F ⊔ (privateEvenCoefficientMap G).range

theorem fullOddRelations_eq_ambient_add_higher (hd : Odd d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    fullOddRelations Q F G=ambientOddRelations Q F G ⊔ (privateHigherRelations G).range := by
  simp only [fullOddRelations,ambientOddRelations,privateEvenCoefficientMap_range hd,sup_assoc]

theorem odd_ambient_covector_dimension (hh : 0 < h) (hm : 0 < m) (hd : Odd d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (G : Fin u → biformParitySpace K h m d 1) :
    finrank K (ambientOddRelations Q F G).dualAnnihilator≤
      finrank K (fullOddRelations Q F G).dualAnnihilator+
        u*∑ r : Fin ((d-1)/2),
          (h+2*(r.val+1)-1).choose (2*(r.val+1))*
            (m+(d-2*(r.val+1))-1).choose (d-2*(r.val+1)) :=
  odd_private_relation_loss hh hm hd G (oddBackgroundRelations Q F)

def mixedPureOddGenerator (hd : Odd d) (U : Forms K h d)
    (P : Forms K h 1 ⊗[K] Forms K m (d-1)) : biformParitySpace K h m d 1 :=
  oddBiformEmbedding (t := d) le_rfl (Nat.odd_iff.mp hd)
    (U ⊗ₜ[K] (⟨1,by
      change (1 : MvPolynomial (Fin m) K).IsHomogeneous (d-d)
      rw [Nat.sub_self]
      exact isHomogeneous_one (Fin m) K⟩ : Forms K m (d-d)))+
  oddBiformEmbedding (t := 1) (by have := hd.pos; omega) (by decide) P

@[simp] theorem mixedPureOddGenerator_val (hd : Odd d) (U : Forms K h d)
    (P : Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (mixedPureOddGenerator hd U P).val=rename Sum.inl U.val+sumBiformMap P := by
  simp [mixedPureOddGenerator,sumBiformMap_tmul]

@[simp] theorem mixedPureHigherRelations_val (hd : Odd d) (U : Fin u → Forms K h d)
    (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : Fin u → HigherEvenCoefficients K h m d) :
    (privateHigherRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) v).val=
      ∑ i,∑ r,(rename Sum.inl (U i).val+sumBiformMap (P i))*sumBiformMap (v i r) := by
  rw [privateHigherRelations_val]
  simp only [mixedPureOddGenerator_val]

end Froberg
