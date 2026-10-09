module

public import Froberg.PreparedRowOpen
public import Froberg.IntrinsicCoefficientRows
public import Froberg.PreparedProductPairs

@[expose] public section

/-! Exact rows in the common coefficient space give the actual polynomial
coefficient rules used by the degree-by-degree elimination. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

/-- An active positive layer is exactly the corresponding slice of the
common scalar-and-layer indexing type. -/
def layerSliceEquiv (R : J) (hR : 0<R.val) :
    Fin (counts R.val) ≃ {i : Label q J counts // degree i=R.val} := by
  classical
  apply Equiv.ofBijective (fun i => ⟨Sum.inr ⟨R,i⟩,rfl⟩)
  constructor
  · intro i k hik
    have h := Sum.inr.inj (congrArg Subtype.val hik)
    simpa using h
  · rintro ⟨a,ha⟩
    cases a with
    | inl i => exact False.elim (by change 0=R.val at ha; omega)
    | inr a =>
      rcases a with ⟨S,i⟩
      have hSR : S=R := Subtype.ext ha
      subst S
      exact ⟨i,rfl⟩

/-- Product columns are independent whenever the full row has only its
mandatory scalar-layer relations. -/
theorem products_injective_of_row_exact
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O)
    (hker : (row hO R p).ker=(rowConstants hO R p).range) :
    Function.Injective (ProductRows.multiplication counts (layers p) J R.val) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro z hz
  change z=0
  change ProductRows.multiplication counts (layers p) J R.val z=0 at hz
  have hx : ((0,0),z)∈(row hO R p).ker := by
    change (∑ i,fullBiformScalarProduct (scalarMap i p) 0)+
      (∑ i,fullBiformScalarProduct 0 (intrinsicLayerMap hO R i p))+
        ProductRows.multiplication counts (layers p) J R.val z=0
    simpa only [map_zero,LinearMap.zero_apply,Finset.sum_const_zero,zero_add] using hz
  rw [hker] at hx
  obtain ⟨C,hC⟩ := hx
  have h := congrArg Prod.snd hC
  exact h.symm

/-- The common prepared row implies the literal scalar/new-layer/product
coefficient identity, using the same generator labels everywhere. -/
theorem coefficient_row_of_exact
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j)
    (R : J) (p : Space n d q J counts O)
    (hker : (row hO R p).ker=(rowConstants hO R p).range) :
    CoefficientRowExact
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (scalar p) (high p) degree R.val := by
  classical
  let e := layerSliceEquiv (q := q) (counts := counts) R (hpos _ R.property)
  let Erow : {i : Label q J counts // degree i=R.val} → FullBiform K σ n R.val (d-R.val) :=
    fun i => intrinsicLayerMap hO R (e.symm i) p
  have hE (i : {i : Label q J counts // degree i=R.val}) :
      high p i.val=(Erow i).val := by
    have hi := congrArg Subtype.val (e.apply_symm_apply i)
    change Sum.inr ⟨R,e.symm i⟩=i.val at hi
    rw [←hi]
    change (p.2 R (e.symm i)).val=layers p R.val (e.symm i)
    simp only [layers,dif_pos R.property]
  have hrow := bilinearKoszulRow_exact_reindex
    (Equiv.refl (Label q J counts)) e.symm fullBiformScalarProduct
    (fun i => scalarMap i p) (fun i => intrinsicLayerMap hO R i p)
    (ProductRows.multiplication counts (layers p) J R.val) hker
  have hcover (i : Label q J counts) (hi : 0<degree i) :
      ∃ a : ProductRows.LayerLabel J counts,Sum.inr a=i := by
    cases i with
    | inl i => exact False.elim (by change 0<0 at hi; omega)
    | inr a => exact ⟨a,rfl⟩
  have hRd := hJ _ R.property
  apply intrinsic_polynomial_coefficient_row_exact
    (by omega : R.val+(d-R.val)=d) degree (fun i => scalarMap i p) (high p)
    Erow hE (ProductRows.multiplication counts (layers p) J R.val) hrow
  · exact ProductRows.prepared_pair_independence (layers p) degree Sum.inr
      Sum.inr_injective (fun _ => rfl) hpos hcover (high p)
      (fun a => (layers_active p a).symm) R.val
      (products_injective_of_row_exact hO R p hker)
  · exact ProductRows.prepared_pair_mem_product_range (layers p) degree Sum.inr
      Sum.inr_injective (fun _ => rfl) hpos hcover (high p)
      (fun a => (layers_active p a).symm) R.val

end Froberg.PreparedParameters
