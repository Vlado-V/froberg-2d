import Froberg.EvenRowWitness
import Froberg.BalancedProductRow
import Froberg.ProductRowUpdate

/-! The finite even-row constructor: the sparse layer and all its product
columns belong to one actual polynomial family and use one scalar list. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

/-- Assemble the odd output space, constrained product witnesses, and the
common scalar open. Every remaining hypothesis is an explicit finite capacity
or the retained-scalar open already established asymptotically. -/
theorem exists_finite_even_row
    {w v d R s b r : ℕ} (hw : 0<w) (hv : 0<v)
    (counts : ℕ → ℕ) (J : Finset ℕ)
    (hpositive : ∀ j∈J,0<j) (heven : ∀ j∈J,Even j) (hdegree : ∀ j∈J,j≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hdiag : ∀ p : ProductRows.Row J R,p.val.val=R-p.val.val →
      counts p.val.val≤(w.choose p.val.val-finrank K X)*(v.choose (d-p.val.val)/2))
    (hcross : ∀ p : ProductRows.Row J R,p.val.val≠R-p.val.val →
      counts p.val.val≤((w+p.val.val-1).choose p.val.val-finrank K X)*(v+(d-p.val.val)-1).choose (d-p.val.val) ∧
      counts (R-p.val.val)≤((w+(R-p.val.val)-1).choose (R-p.val.val)-finrank K X)*
        (v+(d-(R-p.val.val))-1).choose (d-(R-p.val.val)))
    (hodd : 0<oddOutputDimension w R)
    (hm : counts R≤b*(v+v+s-1).choose s)
    (hcap : b*(s+d).choose s≤oddOutputDimension w R)
    (hcount : oddOutputDimension w R*(s+d).choose s *
      (r+oddOutputDimension w R*(v+v+s-1).choose s+
        (oddOutputDimension w R*2^(oddOutputDimension w R))*(v+v+(d-1)-1).choose (d-1)) ≤
      (oddOutputDimension w R-b*(s+d).choose s)*(v+v+s+d-1).choose d)
    (hscalarOpen : ∃ D : MvPolynomial (Fin (finrank K (Fin r → Forms K (v+v) d))) K,
      (∃ Q : Fin r → Forms K (v+v) d,eval (coordinates K _ Q) D≠0) ∧
      ∀ Q : Fin r → Forms K (v+v) d,eval (coordinates K _ Q) D≠0 →
        Function.Injective (ProjectedPrefix.multiplication
          (parityProfileRetained (balancedScalarHalf v) (d%2) (2*((d-R/2)/2))) Q s)) :
    ∃ (o : Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K R)) → MvPolynomial (Fin w × Bool) K)
      (e : Fin (counts R) → Fin (v+v) →₀ ℕ)
      (z : Fin (counts R) → Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K R)) → K),
      ∃ he : ∀ i,(e i).degree=s,
      ∃ (Q : Fin r → Forms K (v+v) d)
        (q : (j : ℕ) → Fin (counts j) → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v)) K),
      LinearIndependent K o ∧ (∀ i,(o i).IsHomogeneous R) ∧
      (∀ i,q R i=attachedPolynomialFamily o e z i) ∧
      (∀ i,(q R i).IsHomogeneous (R+s)) ∧
      (∀ j,j≠R → ∀ i,(q j i).IsHomogeneous d ∧
        (q j i).IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) j ∧
        biformOutputMap (T j) (q j i)=0) ∧
      Function.Injective (homogeneousMultiplication (d := 0) e z he) ∧
      (addRow (polynomialIntermediateRow o e z he Q) (ProductRows.multiplication counts q J R)).ker =
        ((LinearMap.inl K
          ((Fin r → Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K R)) → Forms K (v+v) s) ×
            (Fin (counts R) → Forms K (v+v) d))
          ((Σ p : ProductRows.Row J R,ProductRows.Columns counts p) →₀ K)).comp
            (intermediateKoszul e z he Q)).range := by
  classical
  obtain ⟨O,hO,hOD,hOodd⟩ := exists_odd_output_space (K := K) w R
  have hcoords := homogeneous_output_coordinate_embedding O hO
  rw [hOD] at hcoords
  obtain ⟨o,L,ho,hodeg,hL,hLO⟩ := hcoords
  have hLodd : ∀ z,retainMonomials
      (fun a => Finsupp.weight pairedHalfWeight a%2=0) (outputCombination o (L z))=0 := by
    intro z
    exact hOodd (hLO z)
  obtain ⟨p,hp,hpi⟩ := ProductRows.exists_balanced_product_row hw hv J counts heven hdegree T hdiag hcross
  obtain ⟨e,z,he,Q,hEz,hzero,hker⟩ := exists_even_polynomial_row (by omega) hodd
    pairedHalfWeight (balancedScalarHalf v) o ho hodeg L hL hLodd hm hcap hcount counts p J
    heven hdegree (fun j hj i => (hp j i).2.2.1) (fun j hj i => (hp j i).2.2.2.1) hpi hscalarOpen
  let q := Function.update p R (attachedPolynomialFamily o e (fun i => L (z i)))
  refine ⟨o,e,(fun i => L (z i)),he,Q,q,ho,hodeg,?_,?_,?_,hzero,?_⟩
  · intro i
    exact congrFun (Function.update_self R _ p) i
  · intro i
    simpa only [q,Function.update_self] using hEz i
  · intro j hj i
    simpa only [q,Function.update_of_ne hj] using
      ⟨(hp j i).1,(hp j i).2.1,(hp j i).2.2.2.2⟩
  · change (addRow (polynomialIntermediateRow o e (fun i => L (z i)) he Q)
      (ProductRows.multiplication counts (Function.update p R _) J R)).ker=_
    rw [ProductRows.multiplication_update_self counts p J R hpositive]
    exact hker

end Froberg
