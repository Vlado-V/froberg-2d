module

public import Froberg.ParityEndpointRange

@[expose] public section

/-! The endpoint map on arbitrary finite variable and generator sets, with
literal homogeneous parity coefficients. It is conjugate to the ordinary
endpoint map after enumeration, not an additional relation space. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {σ I : Type} [Fintype I] {n d r : ℕ}

def parityPolynomialProduct (w : σ → ZMod 2) (e p : ZMod 2)
    (g : homogeneousParitySpace K σ d w e) :
    homogeneousParitySpace K σ d w (p-e) →ₗ[K]
      homogeneousParitySpace K σ (2*d) w p where
  toFun a := ⟨g.val*a.val,⟨by
    change (g.val*a.val).IsHomogeneous (2*d)
    simpa only [two_mul] using g.property.1.mul a.property.1,by
    change (g.val*a.val).IsWeightedHomogeneous w p
    have he : e+(p-e)=p := by abel
    simpa only [he] using g.property.2.mul a.property.2⟩⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' c a := Subtype.ext (mul_smul_comm _ _ _)

def parityPolynomialEndpoint (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) (p : ZMod 2) :
    ((i : I) → homogeneousParitySpace K σ d w (p-e i)) →ₗ[K]
      homogeneousParitySpace K σ (2*d) w p :=
  ∑ i,(parityPolynomialProduct w (e i) p (g i)).comp (LinearMap.proj i)

@[simp] theorem parityPolynomialEndpoint_val (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) (p : ZMod 2)
    (a : (i : I) → homogeneousParitySpace K σ d w (p-e i)) :
    (parityPolynomialEndpoint w e g p a).val=∑ i,(g i).val*(a i).val := by
  simp [parityPolynomialEndpoint,parityPolynomialProduct]

def parityPolynomialToFormsEquiv (v : σ ≃ Fin n) (w : σ → ZMod 2) (p : ZMod 2) :
    homogeneousParitySpace K σ d w p ≃ₗ[K]
      parityPartForms (K := K) (d := d) (w ∘ v.symm) p :=
  (homogeneousParityRenameEquiv v w d p).trans (parityPartPolynomialEquiv _ _).symm

@[simp] theorem parityPolynomialToFormsEquiv_val (v : σ ≃ Fin n)
    (w : σ → ZMod 2) (p : ZMod 2) (a : homogeneousParitySpace K σ d w p) :
    (parityPolynomialToFormsEquiv v w p a).val.val=rename v a.val := rfl

def parityEnumeratedForms (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) :
    Fin r → Forms K n d :=
  fun i => (parityPolynomialToFormsEquiv v w (e (j.symm i)) (g (j.symm i))).val

theorem parityEnumeratedForms_homogeneous (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) (i : Fin r) :
    (parityEnumeratedForms v j w e g i).val.IsWeightedHomogeneous
      (w ∘ v.symm) (e (j.symm i)) :=
  (parityPolynomialToFormsEquiv v w (e (j.symm i)) (g (j.symm i))).property

def parityEnumeratedCoefficientsEquiv (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2) (p : ZMod 2) :
    ((i : I) → homogeneousParitySpace K σ d w (p-e i)) ≃ₗ[K]
      ((i : Fin r) → parityPartForms (K := K) (d := d) (w ∘ v.symm) (p-e (j.symm i))) :=
  (LinearEquiv.piCongrRight (fun i => parityPolynomialToFormsEquiv v w (p-e i))).trans
    (LinearEquiv.piCongrLeft' K (fun i => parityPartForms (K := K) (d := d)
      (w ∘ v.symm) (p-e i)) j)

def parityEnumeratedCoefficients (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2) (p : ZMod 2) :
    ((i : I) → homogeneousParitySpace K σ d w (p-e i)) →ₗ[K]
      ((i : Fin r) → parityPartForms (K := K) (d := d) (w ∘ v.symm) (p-e (j.symm i))) :=
  (parityEnumeratedCoefficientsEquiv v j w e p).toLinearMap

theorem parityEnumeratedCoefficients_surjective (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2) (p : ZMod 2) :
    Function.Surjective (parityEnumeratedCoefficients (K := K) (d := d) v j w e p) :=
  (parityEnumeratedCoefficientsEquiv v j w e p).surjective

theorem parityPolynomialEndpoint_transport (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) (p : ZMod 2)
    (a : (i : I) → homogeneousParitySpace K σ d w (p-e i)) :
    parityPolynomialToFormsEquiv v w p (parityPolynomialEndpoint w e g p a)=
      parityEndpointMultiplication (w ∘ v.symm) (e ∘ j.symm)
        (parityEnumeratedForms v j w e g) (parityEnumeratedForms_homogeneous v j w e g) p
        (parityEnumeratedCoefficients v j w e p a) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [parityPolynomialToFormsEquiv_val,parityPolynomialEndpoint_val,map_sum,map_mul,
    parityEndpointMultiplication_val,endpointMultiplication_val]
  change (∑ i,rename v (g i).val*rename v (a i).val)=
    ∑ i,rename v (g (j.symm i)).val*rename v (a (j.symm i)).val
  exact (j.symm.sum_comp (fun i => rename v (g i).val*rename v (a i).val)).symm


theorem parityPolynomialEndpoint_range_transport (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) (p : ZMod 2) :
    (parityPolynomialEndpoint w e g p).range.map
      (parityPolynomialToFormsEquiv v w p).toLinearMap=
      (endpointMultiplication (parityEnumeratedForms v j w e g)).range.comap
        (parityPartForms (w ∘ v.symm) p).subtype := by
  rw [←parityEndpointMultiplication_range (w ∘ v.symm) (e ∘ j.symm)
    (parityEnumeratedForms v j w e g) (parityEnumeratedForms_homogeneous v j w e g) p]
  ext y
  constructor
  · rintro ⟨z,⟨a,rfl⟩,rfl⟩
    exact ⟨parityEnumeratedCoefficients v j w e p a,
      (parityPolynomialEndpoint_transport v j w e g p a).symm⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := parityEnumeratedCoefficients_surjective v j w e p a
    exact ⟨parityPolynomialEndpoint w e g p b,⟨b,rfl⟩,
      parityPolynomialEndpoint_transport v j w e g p b⟩

/-- Quotient by the literal parity-restricted polynomial products agrees
with the odd subspace of the actual degree-`2d` endpoint quotient. -/
def parityPolynomialEndpointQuotientEquiv (v : σ ≃ Fin n) (j : I ≃ Fin r)
    (w : σ → ZMod 2) (e : I → ZMod 2)
    (g : (i : I) → homogeneousParitySpace K σ d w (e i)) :
    (homogeneousParitySpace K σ (2*d) w 1 ⧸ (parityPolynomialEndpoint w e g 1).range) ≃ₗ[K]
      oddTargetSpace (w ∘ v.symm) (parityEnumeratedForms v j w e g) :=
  (Submodule.Quotient.equiv _ _ (parityPolynomialToFormsEquiv v w 1)
    (parityPolynomialEndpoint_range_transport v j w e g 1)).trans
    (endpointOddQuotientEquiv _ _)

end Froberg
