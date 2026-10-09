module

public import Froberg.OddBackgroundRowProjection
public import Froberg.OddAmbientProduct
public import Froberg.MixedPureComponents

@[expose] public section

/-! The mixed pure scalar relations couple only the bottom and top target
rows. Every intermediate odd row therefore retains its actual Q/F
quotient and its scalar growth. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d b q f u : ℕ}

theorem biformTensorComponent_private_product_zero {j : ℕ}
    (hb : b ≤ 2*d) (hbj : b≠j)
    (g : biformParitySpace K h m d 1)
    (hg : g.val.IsWeightedHomogeneous (blockWeight h m) j)
    (p : Forms K h 0 ⊗[K] Forms K m d) :
    biformTensorComponent hb
      (oddPrivateProduct g (evenBiformEmbedding (Nat.zero_le d) (by decide) p))=0 := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,map_zero]
  change weightedHomogeneousComponent (blockWeight h m) b (g.val*sumBiformMap p)=0
  have hp : (sumBiformMap p).IsWeightedHomogeneous (blockWeight h m) 0 :=
    biformImage_output_weight (Forms K h 0) (Forms K m d) le_rfl
      (sumBiformMap_range.le ⟨p,rfl⟩)
  have hgp : (g.val*sumBiformMap p).IsWeightedHomogeneous (blockWeight h m) j := by
    simpa only [Nat.add_zero] using hg.mul hp
  exact hgp.weightedHomogeneousComponent_ne b hbj

theorem biformTensorComponent_privateScalar_zero
    (hd : Odd d) (hb : b ≤ 2*d) (hb1 : b≠1) (hbd : b≠d)
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (z : Fin u → Forms K h 0 ⊗[K] Forms K m d) :
    biformTensorComponent hb (privateScalarRelations (fun i => mixedPureOddGenerator hd (U i) (P i)) z)=0 := by
  apply sumBiformMap_injective
  rw [biformTensorComponent_spec,map_zero]
  rw [privateScalarRelations,LinearMap.comp_apply,privateEvenCoefficientMap_val,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change weightedHomogeneousComponent (blockWeight h m) b
    ((mixedPureOddGenerator hd (U i) (P i)).val*sumBiformMap (z i))=0
  have hp : (sumBiformMap (z i)).IsWeightedHomogeneous (blockWeight h m) 0 :=
    biformImage_output_weight (Forms K h 0) (Forms K m d) le_rfl
      (sumBiformMap_range.le ⟨z i,rfl⟩)
  have he := weighted_component_mul_homogeneous (blockWeight h m)
    (mixedPureOddGenerator hd (U i) (P i)).val (sumBiformMap (z i)) b 0 hp
  simpa only [Nat.add_zero,mixedPureOddGenerator_other hd hb1 hbd,zero_mul] using he


abbrev tensorOddAmbientRelations (hd : Odd d)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :=
  ambientOddRelations (fun i => evenBiformEmbedding (Nat.zero_le d) (by decide) (Q i))
    (fun i => oddBiformEmbedding (by have := hd.pos; omega) (by decide) (F i))
    (fun i => mixedPureOddGenerator hd (U i) (P i))

def oddAmbientRowProjection (hd : Odd d) (hb : 3 ≤ b) (hbd : b<d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    (biformParitySpace K h m (2*d) 1 ⧸ tensorOddAmbientRelations hd Q F U P) →ₗ[K]
      ((OddRowTensor K h m b (2*d-b)) ⧸
        tensorOddRowRelations (b := b) (by omega) (by omega) Q F) :=
  (tensorOddAmbientRelations hd Q F U P).liftQ
    ((tensorOddRowRelations (b := b) (by omega) (by omega) Q F).mkQ.comp
      (biformTensorComponent (by omega))) (by
        apply sup_le
        · intro a ha
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact (oddBackground_tensor_row_range (b := b) (by omega) (by omega) ho Q F).le ⟨a,ha,rfl⟩
        · rintro _ ⟨z,rfl⟩
          change (tensorOddRowRelations (b := b) (by omega) (by omega) Q F).mkQ
            (biformTensorComponent (by omega) (privateScalarRelations _ z))=0
          rw [biformTensorComponent_privateScalar_zero hd (by omega) (by omega) (by omega),map_zero])

@[simp] theorem oddAmbientRowProjection_mk
    (hd : Odd d) (hb : 3 ≤ b) (hbd : b<d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (v : biformParitySpace K h m (2*d) 1) :
    oddAmbientRowProjection hd hb hbd ho Q F U P ((tensorOddAmbientRelations hd Q F U P).mkQ v)=
      (tensorOddRowRelations (b := b) (by omega) (by omega) Q F).mkQ (biformTensorComponent (by omega) v) := rfl

theorem oddAmbientRowProjection_scalar
    (hd : Odd d) (hb : 3 ≤ b) (hbd : b<d) (ho : b%2=1)
    (Q : Fin q → Forms K h 0 ⊗[K] Forms K m d)
    (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K h 0 ⊗[K] Forms K m d) (v : biformParitySpace K h m d 1) :
    oddAmbientRowProjection hd hb hbd ho Q F U P
      ((tensorOddAmbientRelations hd Q F U P).mkQ (tensorScalarParityProduct p v))=
    (tensorOddRowRelations (b := b) (by omega) (by omega) Q F).mkQ
      (oddRowScalarAction (b := b) (by omega) p (biformTensorComponent (by omega) v)) := by
  rw [oddAmbientRowProjection_mk]
  congr 1
  exact biformTensorComponent_scalar_product (by omega) p v

end Froberg
