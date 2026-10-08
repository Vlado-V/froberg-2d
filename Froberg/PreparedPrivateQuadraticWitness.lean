import Froberg.PreparedQuadraticRow
import Froberg.SparseFullOutputDegrees
import Froberg.PreparedExtendedWitness
import Froberg.PreparedPrivateFirstRow

/-! The quadratic sparse witness and a single fixed private detector give
the literal first-row exactness needed by the common private-family open. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]

theorem exists_quadratic_private_row_parameter {a z d q b t h c : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (MvPolynomial σ K)}
    (hd : 3≤d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,2≤j) (hJd : ∀ j∈J,j≤d) (h2 : 2∈J)
    (cap : QuadraticRowCapacity a d q b J counts O)
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K)) (hOT : O 2≤T.ker)
    (w : Fin t → Fin h → K) (ι : Fin t ↪ Fin z)
    (A : Fin t → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (hker : (privatePolynomialMap (a := a) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := d-1) ι w))))
    (P : Fin t → FullBiform K σ (a+z) 1 (d-1))
    (hP : ∀ i,(P i).val=rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell) :
    ∃ p : Space (a+z) d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO ⟨2,h2⟩ i p) ∧
      (privateAugmentedRow hO ⟨2,h2⟩ p (fun i => (P i).val)).ker=
        ((rowConstants hO ⟨2,h2⟩ p).prodMap (intrinsicPrivateBoundary P)).range := by
  classical
  obtain ⟨o,e,v,he,Q,ho,hdeg,hmem,hhom,hzero,hall,hrow⟩ :=
    exists_sparse_full_output_row_all_degrees cap.variables_positive (O 2) (hO 2 h2)
      cap.output_positive cap.enough_generators cap.divisor_capacity cap.incidence cap.scalar_open
  let E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin a) K :=
    Function.update (fun _ _ => 0) 2 (attachedPolynomialFamily o e v)
  have hER : ∀ i,E 2 i=attachedPolynomialFamily o e v i := by simp [E]
  have hEmem : ∀ j∈J,∀ i,E j i∈biformImage (O j) (Forms K a (d-j)) := by
    intro j hj i
    by_cases heq : j=2
    · subst j
      rw [hER]
      exact hmem i
    · rw [show E j i=0 by simp [E,heq]]
      exact Submodule.zero_mem _
  letI : IsEmpty (ProductRows.Row J 2) := ProductRows.first_even_row_empty hJ
  have hrow' := addRow_exact_of_subsingleton (polynomialIntermediateRow o e v he Q)
    (ProductRows.multiplication counts E J 2) (intermediateKoszul e v he Q) hrow
  let p₀ := ofPolynomialFamilies (Q ∘ Fintype.equivFin (Label q J counts)) E hEmem
  let p := coreExtension z p₀
  have hp := sparse_core_extended_parameter_exact (z := z) hO hJd ⟨2,h2⟩ (by change 2<d; omega)
    o ho hdeg e v he Q E hEmem hER hall hrow' ell hell
  refine ⟨p,hp.1,?_⟩
  apply private_first_core_row_exact hd h2 hO bo T w ι A hA hker P hP p₀ _ _ hp.2
  · intro i
    apply biformVectorDetector_eq_zero T (O 2) (Forms K (a+z) (d-2)) hOT
    change layers p 2 i∈biformImage (O 2) (Forms K (a+z) (d-2))
    simpa only [layers,dif_pos h2] using (p.2 ⟨2,h2⟩ i).property
  · apply LinearMap.ext
    intro x
    have hx : x=0 := Subsingleton.elim _ _
    rw [hx,map_zero,LinearMap.zero_apply]

end Froberg.PreparedParameters
