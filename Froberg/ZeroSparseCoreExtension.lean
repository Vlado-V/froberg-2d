import Froberg.SparseCoreExtension

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

 theorem extended_sparse_relation_core_zero (hs : s=0) (hsd : s≤d)
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
  apply extended_mixed_relation_core hsd (fun i j => monomial (e i) (v i j))
    (fun i => (Q i).val) C ?_ (fun t ht => hmat t ht.le) x p hx hp hrel
  intro t ht hts
  have : False := by omega
  exact this.elim

end Froberg
