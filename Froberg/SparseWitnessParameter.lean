import Froberg.PreparedWitnessEmbedding

/-! The explicit parameter supplied by a sparse witness, with its actual
scalar coordinates and layer polynomials retained in the conclusion. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem sparse_witness_parameter_exact
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (R : J)
    (o : Fin (finrank K (homogeneousSubmodule σ K R.val)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R.val)
    (e : Fin (counts R.val) → Fin n →₀ ℕ)
    (v : Fin (counts R.val) → Fin (finrank K (homogeneousSubmodule σ K R.val)) → K)
    (he : ∀ i,(e i).degree=d-R.val)
    (Q : Fin (Fintype.card (Label q J counts)) → Forms K n d)
    (E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (hE : ∀ j∈J,∀ i,E j i∈biformImage (O j) (Forms K n (d-j)))
    (hER : ∀ i,E R.val i=attachedPolynomialFamily o e v i)
    (hzero : Function.Injective (homogeneousMultiplication (d := 0) e v he))
    (hexact : (addRow (polynomialIntermediateRow o e v he Q)
      (ProductRows.multiplication counts E J R.val)).ker=
      ((LinearMap.inl K
        ((Fin (Fintype.card (Label q J counts)) →
          Fin (finrank K (homogeneousSubmodule σ K R.val)) → Forms K n (d-R.val)) ×
          (Fin (counts R.val) → Forms K n d)) (RowProducts (K := K) (J := J) (counts := counts) R.val)).comp
            (intermediateKoszul e v he Q)).range) :
    let p := ofPolynomialFamilies (Q ∘ Fintype.equivFin (Label q J counts)) E hE
    LinearIndependent K (fun i => intrinsicLayerMap hO R i p) ∧
      (row hO R p).ker=(rowConstants hO R p).range := by
  classical
  let f := Fintype.equivFin (Label q J counts)
  let p := ofPolynomialFamilies (Q ∘ f) E hE
  have hpE : (fun i => intrinsicLayerMap hO R i p)=
      (fun i => fullBiformCoordinates o ho hdeg (attachedCoordinates e v he i)) := by
    funext i
    apply Subtype.ext
    change layers p R.val i=polynomialFormVector o (d-R.val) (attachedCoordinates e v he i)
    rw [layers_ofPolynomialFamilies _ _ _ R.property,hER,polynomialFormVector_attachedCoordinates]
  refine ⟨?_,?_⟩
  · rw [hpE]
    exact (attachedCoordinates_independent e v he hzero).map'
      (fullBiformCoordinates o ho hdeg).toLinearMap
      (LinearMap.ker_eq_bot.mpr (fullBiformCoordinates o ho hdeg).injective)
  · have hh := sparse_witness_intrinsic_exact o ho hdeg e v he Q
      (ProductRows.multiplication counts E J R.val) hexact
    have hh' := bilinearKoszulRow_exact_reindex f (Equiv.refl (Fin (counts R.val)))
      fullBiformScalarProduct Q
      (fun i => fullBiformCoordinates o ho hdeg (attachedCoordinates e v he i))
      (ProductRows.multiplication counts E J R.val) hh
    unfold row rowConstants
    rw [hpE,products_ofPolynomialFamilies]
    exact hh'

end Froberg.PreparedParameters
