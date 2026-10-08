import Froberg.FiniteEvenRow
import Froberg.EvenProjectedRow

/-! Finite sparse/product witnesses with every private-output projection
imposed on the very same vector tuple, in a prescribed output basis. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

 theorem homogeneous_output_embedding_basis {σ : Type*} [Fintype σ] {R H : ℕ}
    (bo : Basis (Fin H) K (homogeneousSubmodule σ K R))
    (O : Submodule K (MvPolynomial σ K)) (hO : O≤homogeneousSubmodule σ K R)
    [FiniteDimensional K O] :
    ∃ L : (Fin (finrank K O) → K) →ₗ[K] (Fin H → K),
      Function.Injective L ∧ ∀ z,outputCombination (fun j => (bo j).val) (L z)∈O := by
  let a := Module.finBasis K O
  let f : O →ₗ[K] homogeneousSubmodule σ K R :=
    O.subtype.codRestrict _ (fun x => hO x.property)
  let L := bo.equivFun.toLinearMap.comp (f.comp a.equivFun.symm.toLinearMap)
  refine ⟨L,?_,?_⟩
  · intro x y h
    apply a.equivFun.symm.injective
    apply Subtype.ext
    have hh := congrArg (fun u : homogeneousSubmodule σ K R => u.val) (bo.equivFun.injective h)
    exact hh
  · intro z
    have hb := congrArg Subtype.val (bo.equivFun_symm_apply (L z))
    have hh : outputCombination (fun j => (bo j).val) (L z)=(a.equivFun.symm z).val := by
      simpa only [L,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
        Submodule.coe_sum,Submodule.coe_smul,outputCombination,LinearMap.coe_mk,AddHom.coe_mk,
        f,LinearMap.codRestrict_apply,LinearMap.coe_comp,Submodule.subtype_apply] using hb.symm
    rw [hh]
    exact (a.equivFun.symm z).property

 theorem exists_finite_even_projected_row
    {w v d R s b r H : ℕ} {I : Type*} [Fintype I]
    (hw : 0<w) (hv : 0<v)
    (bo : Basis (Fin H) K (homogeneousSubmodule (Fin w × Bool) K R))
    (Relations : I → Submodule K (Fin H → K))
    (hrelations : ∀ i,b*(s+1).choose s≤oddOutputDimension w R-finrank K (Relations i))
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
    ∃ (e : Fin (counts R) → Fin (v+v) →₀ ℕ) (z : Fin (counts R) → Fin H → K),
      ∃ he : ∀ i,(e i).degree=s,
      ∃ (Q : Fin r → Forms K (v+v) d)
        (q : (j : ℕ) → Fin (counts j) → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v)) K),
      (∀ i c,c≤1 → ∀ p : Fin (counts R) → Forms K (v+v) c,
        (∀ β,sparseOutputCoefficient e z p β∈Relations i) → p=0) ∧
      (∀ i,q R i=attachedPolynomialFamily (fun j => (bo j).val) e z i) ∧
      (∀ i,(q R i).IsHomogeneous (R+s)) ∧
      (∀ j,j≠R → ∀ i,(q j i).IsHomogeneous d ∧
        (q j i).IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) j ∧
        biformOutputMap (T j) (q j i)=0) ∧
      (∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e z he)) ∧
      (addRow (polynomialIntermediateRow (fun j => (bo j).val) e z he Q)
        (ProductRows.multiplication counts q J R)).ker =
        ((LinearMap.inl K ((Fin r → Fin H → Forms K (v+v) s) ×
            (Fin (counts R) → Forms K (v+v) d))
          ((Σ p : ProductRows.Row J R,ProductRows.Columns counts p) →₀ K)).comp
            (intermediateKoszul e z he Q)).range := by
  classical
  letI : FiniteDimensional K (homogeneousSubmodule (Fin w × Bool) K R) :=
    Module.Finite.of_basis bo
  obtain ⟨O,hO,hOD,hOodd⟩ := exists_odd_output_space (K := K) w R
  letI : FiniteDimensional K O := Submodule.finiteDimensional_of_le hO
  have hcoords := homogeneous_output_embedding_basis bo O hO
  rw [hOD] at hcoords
  obtain ⟨L,hL,hLO⟩ := hcoords
  let o := fun j => (bo j).val
  have ho : LinearIndependent K o := bo.linearIndependent.map'
    (homogeneousSubmodule (Fin w × Bool) K R).subtype
    (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _))
  have hLodd : ∀ z,retainMonomials
      (fun a => Finsupp.weight pairedHalfWeight a%2=0) (outputCombination o (L z))=0 :=
    fun z => hOodd (hLO z)
  obtain ⟨p,hp,hpi⟩ := ProductRows.exists_balanced_product_row hw hv J counts heven hdegree T hdiag hcross
  obtain ⟨e,v₀,he,hdiv,hrest⟩ := exists_exact_sparse_intermediate (K := K) (by omega) hodd hm hcap hcount
  obtain ⟨z,Q,hproj,hEz,hzero,hfull,hker⟩ := exists_even_polynomial_row_with_relations
    (by omega) hodd pairedHalfWeight (balancedScalarHalf v) o ho (fun j => (bo j).property)
    L hL hLodd e he hdiv Relations hrelations hcap hcount counts p J heven hdegree
    (fun j hj i => (hp j i).2.2.1) (fun j hj i => (hp j i).2.2.2.1) hpi hscalarOpen
  let q := Function.update p R (attachedPolynomialFamily o e (fun i => L (z i)))
  refine ⟨e,(fun i => L (z i)),he,Q,q,hproj,?_,?_,?_,hfull,?_⟩
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
