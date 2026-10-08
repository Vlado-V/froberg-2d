import Froberg.BiformParitySpaces
import Froberg.ExtraRelationLoss

/-! The remaining C.13 relations are actual products of the mixed pure
generators with positive even biform coefficients. Their image completes
the full odd relation space, so the C.15 loss follows without an extension
assumption. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d u : ℕ}

def oddPrivateProduct (g : biformParitySpace K h m d 1) :
    biformParitySpace K h m d 0 →ₗ[K] biformParitySpace K h m (2*d) 1 where
  toFun v := ⟨g.val*v.val,by
    refine ⟨?_,?_⟩
    · change (g.val*v.val).IsHomogeneous (2*d)
      simpa only [two_mul] using g.property.1.mul v.property.1
    · change (g.val*v.val).IsWeightedHomogeneous (fun i => (blockWeight h m i : ZMod 2)) 1
      simpa only [add_zero] using g.property.2.mul v.property.2⟩
  map_add' v w := Subtype.ext (mul_add _ _ _)
  map_smul' a v := Subtype.ext (mul_smul_comm _ _ _)

def privateEvenCoefficientMap (g : Fin u → biformParitySpace K h m d 1) :
    (Fin u → biformParitySpace K h m d 0) →ₗ[K] biformParitySpace K h m (2*d) 1 :=
  ∑ i,(oddPrivateProduct (g i)).comp (LinearMap.proj i)

@[simp] theorem privateEvenCoefficientMap_val (g : Fin u → biformParitySpace K h m d 1)
    (v : Fin u → biformParitySpace K h m d 0) :
    (privateEvenCoefficientMap g v).val=∑ i,(g i).val*(v i).val := by
  simp [privateEvenCoefficientMap,oddPrivateProduct]

def privateScalarRelations (g : Fin u → biformParitySpace K h m d 1) :
    (Fin u → Forms K h 0 ⊗[K] Forms K m d) →ₗ[K] biformParitySpace K h m (2*d) 1 :=
  (privateEvenCoefficientMap g).comp
    (LinearMap.piMap (fun _ => evenBiformEmbedding (t := 0) (Nat.zero_le d) (by omega)))

def privateHigherRelations (g : Fin u → biformParitySpace K h m d 1) :
    (Fin u → HigherEvenCoefficients K h m d) →ₗ[K] biformParitySpace K h m (2*d) 1 :=
  (privateEvenCoefficientMap g).comp (LinearMap.piMap (fun _ => positiveEvenAssembly))

@[simp] theorem privateHigherRelations_val (g : Fin u → biformParitySpace K h m d 1)
    (v : Fin u → HigherEvenCoefficients K h m d) :
    (privateHigherRelations g v).val=∑ i,∑ r,(g i).val*sumBiformMap (v i r) := by
  simp [privateHigherRelations,Finset.mul_sum]

def privateCoefficientAssembly :
    ((Fin u → Forms K h 0 ⊗[K] Forms K m d) × (Fin u → HigherEvenCoefficients K h m d)) →ₗ[K]
      (Fin u → biformParitySpace K h m d 0) :=
  (LinearMap.piMap (fun _ => evenBiformEmbedding (t := 0) (Nat.zero_le d) (by omega))).coprod
    (LinearMap.piMap (fun _ => positiveEvenAssembly))

theorem privateCoefficientAssembly_surjective (hd : Odd d) :
    Function.Surjective (privateCoefficientAssembly (K := K) (h := h) (m := m) (d := d) (u := u)) := by
  intro v
  choose z hz using fun i => evenCoefficientAssembly_surjective hd (v i)
  refine ⟨(fun i => (z i).1,fun i => (z i).2),?_⟩
  funext i
  exact hz i

theorem privateEvenCoefficientMap_range (hd : Odd d)
    (g : Fin u → biformParitySpace K h m d 1) :
    (privateEvenCoefficientMap g).range=
      (privateScalarRelations g).range ⊔ (privateHigherRelations g).range := by
  have he : (privateScalarRelations g).coprod (privateHigherRelations g)=
      (privateEvenCoefficientMap g).comp privateCoefficientAssembly := by
    apply LinearMap.ext
    intro v
    change privateEvenCoefficientMap g _+privateEvenCoefficientMap g _=
      privateEvenCoefficientMap g (_+_)
    exact (map_add _ _ _).symm
  rw [←LinearMap.range_coprod,he,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (privateCoefficientAssembly_surjective hd),Submodule.map_top]

theorem odd_private_relation_loss (hh : 0 < h) (hm : 0 < m) (hd : Odd d)
    (g : Fin u → biformParitySpace K h m d 1)
    (base : Submodule K (biformParitySpace K h m (2*d) 1)) :
    finrank K (base ⊔ (privateScalarRelations g).range).dualAnnihilator≤
      finrank K (base ⊔ (privateEvenCoefficientMap g).range).dualAnnihilator+
        u*∑ r : Fin ((d-1)/2),
          (h+2*(r.val+1)-1).choose (2*(r.val+1))*
            (m+(d-2*(r.val+1))-1).choose (d-2*(r.val+1)) := by
  have hb := biform_extra_relation_loss (K := K)
    (V := biformParitySpace K h m (2*d) 1) hh hm
    (fun r : Fin ((d-1)/2) => 2*(r.val+1)) (fun r => d-2*(r.val+1))
    (base ⊔ (privateScalarRelations g).range) (privateHigherRelations g)
  rw [privateEvenCoefficientMap_range hd]
  rw [sup_assoc base (privateScalarRelations g).range (privateHigherRelations g).range] at hb
  exact hb

end Froberg
