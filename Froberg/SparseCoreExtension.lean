import Froberg.ExtendedExactRow
import Froberg.PolynomialRowRelations

/-! The exact same sparse even-row witness remains exact after adjoining
private variables: its lower injections and endpoint kernel supply every
hypothesis of the coefficientwise extension argument. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.FreeCoefficients
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {a z s d h m q : ℕ}
variable {W : Type*} [AddCommGroup W] [Module K W]

theorem sparse_endpoint_coordinate_constants
    (o : Fin h → MvPolynomial σ K)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin h → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K a d) (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin a) K)
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K ((Fin q → Fin h → Forms K a s) × (Fin m → Forms K a d)) W).comp
        (intermediateKoszul e v he Q)).range)
    (x : Fin q → Fin h → Poly K a) (p : Fin m → Poly K a)
    (hx : ∀ i j,(x i j).IsHomogeneous s) (hp : ∀ i,(p i).IsHomogeneous d)
    (hrel : ∀ j,(∑ i,(Q i).val*x i j)+(∑ k,monomial (e k) (v k j)*p k)=0) :
    ∃ C : Fin q → Fin m → K,∀ i j,x i j=∑ k,C i k • monomial (e k) (v k j) := by
  let x' : Fin q → Fin h → Forms K a s := fun i j => ⟨x i j,hx i j⟩
  let p' : Fin m → Forms K a d := fun i => ⟨p i,hp i⟩
  have hz : intermediateRow e v he Q (x',p')=0 := by
    funext j
    apply Subtype.ext
    simpa only [intermediateRow,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,
      Submodule.coe_add,BilinearScalarFamily.multiplication_apply,Finset.sum_apply,
      Submodule.coe_sum,vectorMultiply_val,homogeneousMultiplication_val,multiplication_apply,
      x',p',Pi.zero_apply,Submodule.coe_zero] using hrel j
  have hk : ((x',p'),(0:W))∈(addRow (polynomialIntermediateRow o e v he Q) P).ker := by
    change polynomialFormVector o (s+d) (intermediateRow e v he Q (x',p'))+P 0=0
    rw [hz,map_zero,map_zero,add_zero]
  rw [hker] at hk
  obtain ⟨C,hC⟩ := hk
  refine ⟨fun i k => (C i k).val.coeff 0,?_⟩
  intro i j
  have hc := congrArg (fun y : ((Fin q → Fin h → Forms K a s) × (Fin m → Forms K a d)) × W =>
    (y.1.1 i j).val) hC
  change (multiplication e v (C i)) j=x i j at hc
  rw [←hc,multiplication_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [zero_form_eq_C,mul_comm,MvPolynomial.C_mul']

 theorem extended_sparse_relation_core (hs : 1 ≤ s) (hsd : s≤d)
    (o : Fin h → MvPolynomial σ K)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin h → K) (he : ∀ i,(e i).degree=s)
    (Q : Fin q → Forms K a d) (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin a) K)
    (hfull : ∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e v he))
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K ((Fin q → Fin h → Forms K a s) × (Fin m → Forms K a d)) W).comp
        (intermediateKoszul e v he Q)).range)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell)
    (C : Fin h → Poly K a)
    (x : Fin q → Fin h → Poly K (a+z)) (p : Fin m → Poly K (a+z))
    (hx : ∀ i j,(x i j).IsHomogeneous s) (hp : ∀ i,(p i).IsHomogeneous d)
    (hrel : ∀ j,(∑ i,rename (Fin.castAdd z) (Q i).val*x i j)+
      (∑ k,rename (Fin.castAdd z) (monomial (e k) (v k j))*p k)+
      rename (Fin.castAdd z) (C j)=0) :
    (∀ i j,x i j=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) (x i j))) ∧
    (∀ i,p i=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) (p i))) ∧
    ∀ j,(∑ i,(Q i).val*freeCoeff (0 : Fin z →₀ ℕ) (x i j))+
      (∑ k,monomial (e k) (v k j)*freeCoeff (0 : Fin z →₀ ℕ) (p k))+C j=0 := by
  have hmat (t : ℕ) (ht : t≤d) : Function.Injective
      (corePolynomialMatrix (t := t) (fun j i => monomial (e i) (v i j))) := by
    intro p p' hp
    apply hfull t ht
    funext j
    apply Subtype.ext
    exact congrFun hp j
  apply extended_mixed_relation_of_endpoint hs hsd (fun i j => monomial (e i) (v i j))
    (fun i => (Q i).val) C ?_ (fun t ht => hmat t ht.le) ell hell ?_ x p hx hp hrel
  · exact hmat 1 (by omega)
  · exact sparse_endpoint_coordinate_constants o e v he Q P hker

end Froberg
