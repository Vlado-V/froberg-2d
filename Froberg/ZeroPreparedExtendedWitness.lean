module

public import Froberg.SparseWitnessParameter
public import Froberg.ZeroExtendedIntrinsicRow
public import Froberg.PreparedProductBiform

@[expose] public section

/-! The sparse witness is an exact point of the actual prepared parameter
space after adjoining the fixed private variables. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

 theorem sparse_core_extended_parameter_exact_zero
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : J) (hRd : R.val=d)
    (o : Fin (finrank K (homogeneousSubmodule σ K R.val)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R.val)
    (e : Fin (counts R.val) → Fin a →₀ ℕ)
    (v : Fin (counts R.val) → Fin (finrank K (homogeneousSubmodule σ K R.val)) → K)
    (he : ∀ i,(e i).degree=d-R.val)
    (Q : Fin (Fintype.card (Label q J counts)) → Forms K a d)
    (E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin a) K)
    (hE : ∀ j∈J,∀ i,E j i∈biformImage (O j) (Forms K a (d-j)))
    (hER : ∀ i,E R.val i=attachedPolynomialFamily o e v i)
    (hfull : ∀ c ≤ d,Function.Injective (homogeneousMultiplication (d := c) e v he))
    (hker : (addRow (polynomialIntermediateRow o e v he Q)
      (ProductRows.multiplication counts E J R.val)).ker=
      ((LinearMap.inl K
        ((Fin (Fintype.card (Label q J counts)) → Fin (finrank K (homogeneousSubmodule σ K R.val)) → Forms K a (d-R.val)) ×
          (Fin (counts R.val) → Forms K a d)) (RowProducts (K := K) (J := J) (counts := counts) R.val)).comp
            (intermediateKoszul e v he Q)).range)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell) :
    let p := coreExtension z (ofPolynomialFamilies (Q ∘ Fintype.equivFin (Label q J counts)) E hE)
    LinearIndependent K (fun i => intrinsicLayerMap hO R i p) ∧
      (row hO R p).ker=(rowConstants hO R p).range := by
  classical
  let f := Fintype.equivFin (Label q J counts)
  let p₀ := ofPolynomialFamilies (Q ∘ f) E hE
  let p := coreExtension z p₀
  have hp₀ := sparse_witness_parameter_exact hO R o ho hdeg e v he Q E hE hER (hfull 0 (by omega)) hker
  have hproducts : (ProductRows.multiplication counts E J R.val).range≤
      FullBiform K σ a R.val ((d-R.val)+d) := by
    have hh := ProductRows.multiplication_range_full_biform E (by omega : R.val≤2*d)
      (by
        intro j hj i
        have hh := biformImage_homogeneous _ _ (hO j hj) le_rfl (hE j hj i)
        change (E j i).IsHomogeneous (j+(d-j)) at hh
        simpa only [Nat.add_sub_of_le (hJ j hj)] using hh)
      (fun j hj i => biformImage_output_weight _ _ (hO j hj) (hE j hj i))
    convert hh using 1 <;> congr 2 <;> omega
  have hext := extended_sparse_intrinsic_exact_zero (z := z) (by omega : d-R.val=0) (by omega : d-R.val≤d)
    o ho hdeg e v he Q (ProductRows.multiplication counts E J R.val) hproducts hfull hker ell hell
  let Q' : Fin (Fintype.card (Label q J counts)) → Forms K (a+z) d := fun i =>
    ⟨rename (Fin.castAdd z) (Q i).val,(Q i).property.rename_isHomogeneous⟩
  let E' : Fin (counts R.val) → FullBiform K σ (a+z) R.val (d-R.val) := fun i =>
    ⟨rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v i),
      biformImage_core_extension _ (by
        rw [←polynomialFormVector_attachedCoordinates o e v he i]
        exact polynomialFormVector_mem_biform o _ _ hdeg _ (fun j => (attachedCoordinates e v he i j).property))⟩
  let P' := (rename (Sum.map id (Fin.castAdd z))).toLinearMap.comp
    (ProductRows.multiplication counts E J R.val)
  have hE' : (fun i => intrinsicLayerMap hO R i p)=E' := by
    funext i
    apply Subtype.ext
    change layers p R.val i=rename (Sum.map id (Fin.castAdd z)) (attachedPolynomialFamily o e v i)
    rw [show p=coreExtension z p₀ from rfl,coreExtension_layers]
    dsimp only
    rw [show p₀=ofPolynomialFamilies (Q ∘ f) E hE from rfl,
      layers_ofPolynomialFamilies _ _ _ R.property,hER]
  have hP' : ProductRows.multiplication counts (layers p) J R.val=P' := by
    rw [show p=coreExtension z p₀ from rfl,coreExtension_products,products_ofPolynomialFamilies]
  constructor
  · have hb : LinearIndependent K (fun i => (intrinsicLayerMap hO R i p₀).val) :=
      hp₀.1.map' (FullBiform K σ a R.val (d-R.val)).subtype (Submodule.ker_subtype _)
    have hr := hb.map' (rename (Sum.map id (Fin.castAdd z))).toLinearMap
      (LinearMap.ker_eq_bot.mpr (rename_injective _
        (Function.Injective.sumMap (fun _ _ h => h) (Fin.castAdd_injective a z))))
    apply LinearIndependent.of_comp (FullBiform K σ (a+z) R.val (d-R.val)).subtype
    convert hr using 1
    funext i
    change layers p R.val i=rename (Sum.map id (Fin.castAdd z)) (layers p₀ R.val i)
    exact congrFun (congrFun (coreExtension_layers (z := z) p₀) R.val) i
  · have hext' : (bilinearKoszulRow fullBiformScalarProduct Q' E' P').ker=
        (bilinearKoszulConstants (K := K) (W := RowProducts (K := K) (J := J) (counts := counts) R.val) Q' E').range := hext
    have hr := bilinearKoszulRow_exact_reindex f (Equiv.refl (Fin (counts R.val)))
      fullBiformScalarProduct Q' E' P' hext'
    unfold row rowConstants
    rw [hE',hP']
    exact hr

end Froberg.PreparedParameters
