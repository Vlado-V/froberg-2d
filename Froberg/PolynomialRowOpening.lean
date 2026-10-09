module

public import Froberg.BilinearKoszulRow
public import Froberg.PolynomialRowRelations

@[expose] public section

/-! Sparse polynomial witnesses belong to the unrestricted coefficient row
family. This is the bridge from finite row constructions to common opens. -/
noncomputable section
namespace Froberg
open Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ I J W : Type*} [Fintype I] [Fintype J]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {n s d q : ℕ}

def coordinateScalarProduct (o : J → MvPolynomial σ K) :
    Forms K n d →ₗ[K] (J → Forms K n s) →ₗ[K] MvPolynomial (σ ⊕ Fin n) K where
  toFun f := (polynomialFormVector o (s+d)).comp (vectorMultiply f)
  map_add' f g := by simp only [map_add,LinearMap.comp_add]
  map_smul' c f := by simp only [map_smul,LinearMap.comp_smul,RingHom.id_apply]

@[simp] theorem coordinateScalarProduct_apply (o : J → MvPolynomial σ K)
    (f : Forms K n d) (u : J → Forms K n s) :
    coordinateScalarProduct o f u=rename Sum.inr f.val*polynomialFormVector o s u :=
  polynomialFormVector_vectorMultiply o f u

def attachedCoordinates (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) (i : I) : J → Forms K n s :=
  fun j => ⟨monomial (e i) (v i j),isHomogeneous_monomial _ (he i)⟩

@[simp] theorem polynomialFormVector_attachedCoordinates (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s) (i : I) :
    polynomialFormVector o s (attachedCoordinates e v he i)=attachedPolynomialFamily o e v i := rfl

/-- The unrestricted coefficient row specializes to the actual sparse row. -/
theorem bilinearKoszulRow_attached (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d) (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K) :
    bilinearKoszulRow (coordinateScalarProduct o) Q (attachedCoordinates e v he) P=
      addRow (polynomialIntermediateRow o e v he Q) P := by
  apply LinearMap.ext
  intro x
  change (∑ i,coordinateScalarProduct o (Q i) (x.1.1 i))+
    (∑ i,coordinateScalarProduct o (x.1.2 i) (attachedCoordinates e v he i))+P x.2=_
  rw [polynomialIntermediateRow_eq_addRow,addRow_apply,addRow_apply,polynomialLayerRow_apply]
  have hscalar : polynomialScalarRow o Q x.1.1=∑ i,coordinateScalarProduct o (Q i) (x.1.1 i) := by
    unfold polynomialScalarRow
    rw [LinearMap.comp_apply,BilinearScalarFamily.multiplication_apply,map_sum]
    rfl
  rw [hscalar]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinateScalarProduct_apply,polynomialFormVector_attachedCoordinates,mul_comm]

/-- Degree-zero homogeneous coefficients are precisely the field constants
in the mandatory relation map. -/
theorem intermediateKoszul_eq_constants (e : I → Fin n →₀ ℕ)
    (v : I → J → K) (he : ∀ i,(e i).degree=s) (Q : Fin q → Forms K n d)
    (c : Fin q → I → Forms K n 0) :
    ((LinearMap.inl K ((Fin q → J → Forms K n s) × (I → Forms K n d)) W).comp
      (intermediateKoszul e v he Q)) c=
      bilinearKoszulConstants (W := W) Q (attachedCoordinates e v he)
        (fun i a => (c i a).val.coeff 0) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i j
      apply Subtype.ext
      change (homogeneousMultiplication (d := 0) e v he (c i) j).val=
        ((∑ a,(c i a).val.coeff 0 • attachedCoordinates e v he a) j).val
      simp only [homogeneousMultiplication_val,multiplication_apply,Finset.sum_apply,
        Pi.smul_apply,Submodule.coe_sum,Submodule.coe_smul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [zero_form_eq_C,mul_comm,MvPolynomial.C_mul']
      simp [attachedCoordinates]
    · funext a
      apply Subtype.ext
      change ((-∑ i,fun a => constantMul (Q i) (c i a)) a).val=
        (-∑ i,(c i a).val.coeff 0 • Q i).val
      simp only [Pi.neg_apply,Finset.sum_apply,Submodule.coe_neg,Submodule.coe_sum,
        Submodule.coe_smul,constantMul_val]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [zero_form_eq_C,mul_comm,MvPolynomial.C_mul']
      simp
  · rfl

theorem intermediateKoszul_range_eq_constants (e : I → Fin n →₀ ℕ)
    (v : I → J → K) (he : ∀ i,(e i).degree=s) (Q : Fin q → Forms K n d) :
    ((LinearMap.inl K ((Fin q → J → Forms K n s) × (I → Forms K n d)) W).comp
      (intermediateKoszul e v he Q)).range=
      (bilinearKoszulConstants (W := W) Q (attachedCoordinates e v he)).range := by
  apply le_antisymm
  · rintro x ⟨c,rfl⟩
    exact ⟨_,(intermediateKoszul_eq_constants e v he Q c).symm⟩
  · rintro x ⟨C,rfl⟩
    let c : Fin q → I → Forms K n 0 := fun i a => ⟨MvPolynomial.C (C i a),isHomogeneous_C _ _⟩
    refine ⟨c,?_⟩
    rw [intermediateKoszul_eq_constants]
    congr 1
    funext i a
    simp [c]

/-- The finite sparse exactness witness is already an exact unrestricted
coefficient row, ready for the common-parameter openness theorem. -/
theorem sparse_witness_unrestricted_exact (o : J → MvPolynomial σ K)
    (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K n d) (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K ((Fin q → J → Forms K n s) × (I → Forms K n d)) W).comp
        (intermediateKoszul e v he Q)).range) :
    (bilinearKoszulRow (coordinateScalarProduct o) Q (attachedCoordinates e v he) P).ker=
      (bilinearKoszulConstants (W := W) Q (attachedCoordinates e v he)).range := by
  rw [bilinearKoszulRow_attached,hker,intermediateKoszul_range_eq_constants]

/-- The degree-zero sparse injection supplies independence of the unrestricted
new-layer coefficient vectors, hence the mandatory-kernel dimension. -/
theorem attachedCoordinates_independent (e : I → Fin n →₀ ℕ)
    (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (hinj : Function.Injective (homogeneousMultiplication (d := 0) e v he)) :
    LinearIndependent K (attachedCoordinates e v he) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let c : I → Forms K n 0 := fun a => ⟨MvPolynomial.C (g a),isHomogeneous_C _ _⟩
  have hmul : homogeneousMultiplication (d := 0) e v he c=∑ a,g a • attachedCoordinates e v he a := by
    funext j
    apply Subtype.ext
    simp only [homogeneousMultiplication_val,multiplication_apply,Finset.sum_apply,
      Pi.smul_apply,Submodule.coe_sum,Submodule.coe_smul]
    change (∑ a,monomial (e a) (v a j)*MvPolynomial.C (g a))=
      (∑ a,g a • (attachedCoordinates e v he a j).val)
    apply Finset.sum_congr rfl
    intro a ha
    rw [mul_comm,MvPolynomial.C_mul']
    rfl
  have hc : c=0 := hinj (by rw [hmul,hg,map_zero])
  have hci := congrArg (fun f : I → Forms K n 0 => (f i).val.coeff 0) hc
  simpa [c] using hci

end Froberg
