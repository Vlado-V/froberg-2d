module

public import Froberg.ExtendedMixedRow

@[expose] public section

/-! Endpoint exactness supplies all lower mixed rows needed to adjoin the
private variables. The core-only product term is kept literally unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial Quartic.FreeCoefficients
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
variable {a z q s d : ℕ}

theorem extended_mixed_relation_of_endpoint (hs : 1 ≤ s) (hsd : s≤d)
    (E : I → J → Poly K a) (Q : Fin q → Poly K a) (C : J → Poly K a)
    (hlinear : Function.Injective (linearVectorCombination E))
    (hEinj : ∀ t,t<d → Function.Injective (corePolynomialMatrix (t := t) (fun j i => E i j)))
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell)
    (hendpoint : ∀ (x : Fin q → J → Poly K a) (p : I → Poly K a),
      (∀ i j,(x i j).IsHomogeneous s) → (∀ i,(p i).IsHomogeneous d) →
      (∀ j,(∑ i,Q i*x i j)+(∑ k,E k j*p k)=0) →
      ∃ B : Fin q → I → K,∀ i j,x i j=∑ k,B i k • E k j)
    (x : Fin q → J → Poly K (a+z)) (p : I → Poly K (a+z))
    (hx : ∀ i j,(x i j).IsHomogeneous s)
    (hp : ∀ i,(p i).IsHomogeneous d)
    (hrel : ∀ j,(∑ i,rename (Fin.castAdd z) (Q i)*x i j)+
      (∑ k,rename (Fin.castAdd z) (E k j)*p k)+rename (Fin.castAdd z) (C j)=0) :
    (∀ i j,x i j=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) (x i j))) ∧
    (∀ i,p i=rename (Fin.castAdd z) (freeCoeff (0 : Fin z →₀ ℕ) (p i))) ∧
    ∀ j,(∑ i,Q i*freeCoeff (0 : Fin z →₀ ℕ) (x i j))+
      (∑ k,E k j*freeCoeff (0 : Fin z →₀ ℕ) (p k))+C j=0 := by
  have hbelow₁ := lower_mixed_row_zero hs (by omega : 1≤d) E Q hlinear
    (hEinj (d-1) (by omega)) ell hell hendpoint
  apply extended_mixed_relation_core hsd E Q C ?_ hEinj x p hx hp hrel
  intro t ht hts x' p' hx' hp' hrel'
  exact mixed_row_lower_zero E Q hbelow₁ (ell 0) (hell.ne_zero 0)
    (by omega : s-t≤ s-1) (by omega : d-t≤d-1)
    (by omega : s-1-(s-t)=d-1-(d-t)) x' p' hx' hp' hrel'

end Froberg
