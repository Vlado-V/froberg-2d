import Froberg.SingleProfileEvenWitness
import Froberg.SingleDiagonalRow
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
theorem exists_finite_fourth_row
    {w v d s b r : ℕ} (hw : 0<w) (hv : 0<v)
    (counts : ℕ → ℕ) (J : Finset ℕ)
    (hpositive : ∀ j∈J,0<j) (heven : ∀ j∈J,Even j) (hdegree : ∀ j∈J,j≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hlow : ∀ j∈J,2≤j)
    (hdiag₂ : counts 2≤(w.choose 2-finrank K X)*(v.choose (d-2)/2))
    (hodd : 0<oddOutputDimension w 4)
    (hm : counts 4≤b*(v+v+s-1).choose s)
    (hcap : b*(s+d).choose s≤oddOutputDimension w 4)
    (hcount : oddOutputDimension w 4*(s+d).choose s *
      (r+oddOutputDimension w 4*(v+v+s-1).choose s+
        (oddOutputDimension w 4*2^(oddOutputDimension w 4))*(v+v+(d-1)-1).choose (d-1)) ≤
      (oddOutputDimension w 4-b*(s+d).choose s)*(v+v+s+d-1).choose d)
    (hscalarOpen : ∃ D : MvPolynomial (Fin (finrank K (Fin r → Forms K (v+v) d))) K,
      (∃ Q : Fin r → Forms K (v+v) d,eval (coordinates K _ Q) D≠0) ∧
      ∀ Q : Fin r → Forms K (v+v) d,eval (coordinates K _ Q) D≠0 →
        Function.Injective (ProjectedPrefix.multiplication
          (fun α => MonomialExpansion.partialDegree (balancedScalarHalf v) α≠2*((d-2)/2)) Q s)) :
    ∃ (o : Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K 4)) → MvPolynomial (Fin w × Bool) K)
      (e : Fin (counts 4) → Fin (v+v) →₀ ℕ)
      (z : Fin (counts 4) → Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K 4)) → K),
      ∃ he : ∀ i,(e i).degree=s,
      ∃ (Q : Fin r → Forms K (v+v) d)
        (q : (j : ℕ) → Fin (counts j) → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v)) K),
      LinearIndependent K o ∧ (∀ i,(o i).IsHomogeneous 4) ∧
      (∀ i,q 4 i=attachedPolynomialFamily o e z i) ∧
      (∀ i,(q 4 i).IsHomogeneous (4+s)) ∧
      (∀ j,j≠4 → ∀ i,(q j i).IsHomogeneous d ∧
        (q j i).IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) j ∧
        biformOutputMap (T j) (q j i)=0) ∧
      (∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e z he)) ∧
      (addRow (polynomialIntermediateRow o e z he Q) (ProductRows.multiplication counts q J 4)).ker =
        ((LinearMap.inl K
          ((Fin r → Fin (finrank K (homogeneousSubmodule (Fin w × Bool) K 4)) → Forms K (v+v) s) ×
            (Fin (counts 4) → Forms K (v+v) d))
          ((Σ p : ProductRows.Row J 4,ProductRows.Columns counts p) →₀ K)).comp
            (intermediateKoszul e z he Q)).range := by
  classical
  obtain ⟨O,hO,hOD,hOodd⟩ := exists_odd_output_space (K := K) w 4
  have hcoords := homogeneous_output_coordinate_embedding O hO
  rw [hOD] at hcoords
  obtain ⟨o,L,ho,hodeg,hL,hLO⟩ := hcoords
  have hLodd : ∀ z,retainMonomials
      (fun a => Finsupp.weight pairedHalfWeight a%2=0) (outputCombination o (L z))=0 := by
    intro z
    exact hOodd (hLO z)
  have hsecond (p : ProductRows.Row J 4) : p.val.val=2 := by
    have ha := hlow _ p.property.1
    have hb := hlow _ p.property.2.1
    omega
  obtain ⟨p,hp,hpi⟩ := ProductRows.exists_balanced_product_row hw hv J counts heven hdegree T
    (by intro t ht; simpa only [hsecond t] using hdiag₂)
    (by intro t ht; have hh := hsecond t; omega)
  have hPX := ProductRows.product_row_even_projection pairedHalfWeight counts p heven
    (fun j hj i => (hp j i).2.2.1)
  have hPair : ∀ a,(pairProducts (p 2) a).IsWeightedHomogeneous
      (Sum.elim (fun _ : Fin w × Bool => 0) (ProductRows.halfWeight (balancedScalarHalf v)))
      (2*((d-2)/2)) := by
    intro a
    induction a using Sym2.inductionOn with
    | _ x y =>
      have hx := (hp 2 x).2.2.2.1
      have hy := (hp 2 y).2.2.2.1
      simpa only [ProductRows.assignedScalarDegree,show ¬2*2<4 by omega,
        show 2*2=4 by omega,if_false,if_true,pairProducts_mk,two_mul] using hx.mul hy
  have hPY : ∀ a,(ProductRows.multiplication counts p J 4 a).IsWeightedHomogeneous
      (Sum.elim (fun _ : Fin w × Bool => 0) (ProductRows.halfWeight (balancedScalarHalf v)))
      (2*((d-2)/2)) := by
    intro a
    exact ProductRows.multiplication_single_diagonal_row_range counts J 2 p
      (fun r _ => hsecond r)
      (weightedHomogeneousSubmodule K
        (Sum.elim (fun _ : Fin w × Bool => 0) (ProductRows.halfWeight (balancedScalarHalf v)))
        (2*((d-2)/2))) hPair (LinearMap.mem_range_self _ a)
  obtain ⟨e,z,he,Q,hEz,hzero,hker⟩ := exists_single_profile_even_polynomial_row (by omega) hodd
    pairedHalfWeight (balancedScalarHalf v) o ho hodeg L hL hLodd hm hcap hcount
    (ProductRows.multiplication counts p J 4) hpi hPX hPY hscalarOpen
  let q := Function.update p 4 (attachedPolynomialFamily o e (fun i => L (z i)))
  refine ⟨o,e,(fun i => L (z i)),he,Q,q,ho,hodeg,?_,?_,?_,hzero,?_⟩
  · intro i
    exact congrFun (Function.update_self 4 _ p) i
  · intro i
    simpa only [q,Function.update_self] using hEz i
  · intro j hj i
    simpa only [q,Function.update_of_ne hj] using
      ⟨(hp j i).1,(hp j i).2.1,(hp j i).2.2.2.2⟩
  · change (addRow (polynomialIntermediateRow o e (fun i => L (z i)) he Q)
      (ProductRows.multiplication counts (Function.update p 4 _) J 4)).ker=_
    rw [ProductRows.multiplication_update_self counts p J 4 hpositive]
    exact hker

end Froberg
