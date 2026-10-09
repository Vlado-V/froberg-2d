module

public import Froberg.ParityRangeQuotient

@[expose] public section

/-! The odd part of the full endpoint product relation space is exactly
the image obtained using coefficient parity opposite to each generator. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K : Type} [Field K] {n d r : ℕ}

def parityCoefficientInclusion (w : Fin n → ZMod 2) (e : Fin r → ZMod 2) (p : ZMod 2) :
    ((i : Fin r) → parityPartForms (K := K) (d := d) w (p-e i)) →ₗ[K] (Fin r → Forms K n d) :=
  LinearMap.pi (fun i => (parityPartForms w (p-e i)).subtype.comp (LinearMap.proj i))

@[simp] theorem paritySource_inclusion (w : Fin n → ZMod 2) (e : Fin r → ZMod 2) (p : ZMod 2)
    (a : (i : Fin r) → parityPartForms (K := K) (d := d) w (p-e i)) :
    paritySource w e p (parityCoefficientInclusion w e p a)=parityCoefficientInclusion w e p a := by
  funext i
  exact parityForm_same w (p-e i) (a i).val (a i).property

def parityEndpointMultiplication (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) (p : ZMod 2) :
    ((i : Fin r) → parityPartForms (K := K) (d := d) w (p-e i)) →ₗ[K]
      parityPartForms (K := K) (d := 2*d) w p :=
  ((endpointMultiplication q).comp (parityCoefficientInclusion w e p)).codRestrict _ (by
    intro a
    rw [←parityForm_range]
    refine ⟨endpointMultiplication q (parityCoefficientInclusion w e p a),?_⟩
    rw [←endpointMultiplication_paritySource w e q hq,paritySource_inclusion]
    rfl)

@[simp] theorem parityEndpointMultiplication_val (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) (p : ZMod 2)
    (a : (i : Fin r) → parityPartForms (K := K) (d := d) w (p-e i)) :
    (parityEndpointMultiplication w e q hq p a).val=
      endpointMultiplication q (parityCoefficientInclusion w e p a) := rfl

theorem parityEndpointMultiplication_range (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i)) (p : ZMod 2) :
    (parityEndpointMultiplication w e q hq p).range=
      (endpointMultiplication q).range.comap (parityPartForms w p).subtype := by
  ext v
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨parityCoefficientInclusion w e p a,rfl⟩
  · rintro ⟨a,ha⟩
    let b : (i : Fin r) → parityPartForms (K := K) (d := d) w (p-e i) :=
      fun i => ⟨parityForm w (p-e i) (a i),parityForm_homogeneous w (p-e i) (a i)⟩
    refine ⟨b,?_⟩
    apply Subtype.ext
    change endpointMultiplication q (paritySource w e p a)=v.val
    rw [endpointMultiplication_paritySource w e q hq,ha]
    exact parityForm_same w p v.val v.property

end Froberg
