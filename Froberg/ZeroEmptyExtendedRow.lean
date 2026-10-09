module

public import Froberg.ZeroPreparedExtendedWitness

@[expose] public section

/-! An inactive ordinary row remains exact after adding private variables,
and its empty new-layer block separates every prescribed private column. -/
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem empty_row_core_extended_exact_zero
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : J) (hRd : R.val=d)
    (hz : counts R.val=0) (p₀ : Space a d q J counts O)
    (hcore : (row hO R p₀).ker=(rowConstants hO R p₀).range)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell) :
    (row hO R (coreExtension z p₀)).ker=
      (rowConstants hO R (coreExtension z p₀)).range := by
  classical
  letI : IsEmpty (Fin (counts R.val)) := ⟨fun i => by have := i.isLt; omega⟩
  letI : Module.Finite K (homogeneousSubmodule σ K R.val) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ R.val)
  let bo := Module.finBasis K (homogeneousSubmodule σ K R.val)
  let o := fun i => (bo i).val
  have ho : LinearIndependent K o := bo.linearIndependent.map'
    (homogeneousSubmodule σ K R.val).subtype (Submodule.ker_subtype _)
  have hdeg : ∀ i,(o i).IsHomogeneous R.val := fun i => (bo i).property
  let f := Fintype.equivFin (Label q J counts)
  let Q : Fin (Fintype.card (Label q J counts)) → Forms K a d :=
    fun i => scalarMap (f.symm i) p₀
  let e : Fin (counts R.val) → Fin a →₀ ℕ := isEmptyElim
  let v : Fin (counts R.val) → Fin (finrank K (homogeneousSubmodule σ K R.val)) → K :=
    isEmptyElim
  have he : ∀ i,(e i).degree=d-R.val := fun i => isEmptyElim i
  have hE : ∀ j∈J,∀ i,layers p₀ j i∈biformImage (O j) (Forms K a (d-j)) := by
    intro j hj i
    simpa only [layers,dif_pos hj] using (p₀.2 ⟨j,hj⟩ i).property
  let c := fullBiformCoordinates (n := a) (s := d-R.val) o ho hdeg
  have hidx := bilinearKoszulRow_exact_reindex f.symm (Equiv.refl (Fin (counts R.val)))
    fullBiformScalarProduct (fun i => scalarMap i p₀) (fun i => intrinsicLayerMap hO R i p₀)
    (ProductRows.multiplication counts (layers p₀) J R.val) hcore
  have hμ : ∀ (g : Forms K a d) (u : FullBiform K σ a R.val (d-R.val)),
      coordinateScalarProduct o g (c.symm u)=fullBiformScalarProduct g u := by
    intro g u
    rw [coordinateScalarProduct_apply,fullBiformScalarProduct_apply]
    change rename Sum.inr g.val*(c (c.symm u)).val=rename Sum.inr g.val*u.val
    rw [c.apply_symm_apply]
  have hc := bilinearKoszulRow_exact_transport c.symm fullBiformScalarProduct
    (coordinateScalarProduct o) hμ Q (fun i => intrinsicLayerMap hO R i p₀)
    (ProductRows.multiplication counts (layers p₀) J R.val) hidx
  have hEc : (fun i => c.symm (intrinsicLayerMap hO R i p₀))=attachedCoordinates e v he := by
    funext i
    exact isEmptyElim i
  rw [hEc,bilinearKoszulRow_attached] at hc
  have hker : (addRow (polynomialIntermediateRow o e v he Q)
      (ProductRows.multiplication counts (layers p₀) J R.val)).ker=
      ((LinearMap.inl K
        ((Fin (Fintype.card (Label q J counts)) → Fin (finrank K (homogeneousSubmodule σ K R.val)) → Forms K a (d-R.val)) ×
          (Fin (counts R.val) → Forms K a d)) (RowProducts (K := K) (J := J) (counts := counts) R.val)).comp
            (intermediateKoszul e v he Q)).range := by
    rw [intermediateKoszul_range_eq_constants]
    exact hc
  have hext := sparse_core_extended_parameter_exact_zero (z := z) hO hJ R hRd o ho hdeg e v he Q
    (layers p₀) hE (fun i => isEmptyElim i)
    (fun _ _ _ _ _ => Subsingleton.elim _ _) hker ell hell
  have hp : ofPolynomialFamilies (Q ∘ f) (layers p₀) hE=p₀ := by
    apply Prod.ext
    · funext i
      change scalarMap (f.symm (f i)) p₀=p₀.1 i
      rw [f.symm_apply_apply]
      rfl
    · funext j i
      apply Subtype.ext
      simp only [ofPolynomialFamilies,layers,dif_pos j.property]
  have hext' : (row hO R (coreExtension z (ofPolynomialFamilies (Q ∘ f) (layers p₀) hE))).ker=
      (rowConstants hO R (coreExtension z (ofPolynomialFamilies (Q ∘ f) (layers p₀) hE))).range := hext.2
  rw [hp] at hext'
  exact hext'

end Froberg.PreparedParameters
