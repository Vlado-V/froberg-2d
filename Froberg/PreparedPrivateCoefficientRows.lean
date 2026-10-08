import Froberg.PreparedCoefficientRows
import Froberg.PreparedPrivateRowOpen

/-! The open intrinsic augmented-row conditions imply the literal
coefficient equations used by delayed private elimination. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_coefficient_row_of_separated
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j)
    (R : J) (p : Space n d q J counts O)
    (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hsep : ∀ x u,row hO R p x+privateRowMap (d := d) P R.val u=0 → u=0) :
    PrivateRowSeparation
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (scalar p) (high p) P degree R.val := by
  classical
  intro x f B u hx hf hu hB hrel
  have hRd := hJ _ R.property
  have hx' (i) : x i∈FullBiform K σ n R.val (d-R.val) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_sub_of_le hRd] using (show (x i).IsHomogeneous d from (hx i).1)
    · exact (hx i).2
  have hu' (i) : u i∈FullBiform K σ n (R.val-1) (d-(R.val-1)) := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_sub_of_le (by omega : R.val-1≤d)] using (show (u i).IsHomogeneous d from (hu i).1)
    · exact (hu i).2
  choose f' hf' using fun i => homogeneous_output_zero_exists (hf i).1 (hf i).2
  let C := ∑ i,∑ k,B i k • (high p i*high p k)
  have hcover (i : Label q J counts) (hi : 0<degree i) :
      ∃ a : ProductRows.LayerLabel J counts,Sum.inr a=i := by
    cases i with
    | inl i => exact False.elim (by change 0<0 at hi; omega)
    | inr a => exact ⟨a,rfl⟩
  have hC : C∈(ProductRows.multiplication counts (layers p) J R.val).range := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    by_cases hik : 0<degree i ∧ 0<degree k ∧ degree i+degree k=R.val
    · apply Submodule.smul_mem
      exact ProductRows.prepared_pair_mem_product_range (layers p) degree Sum.inr
        Sum.inr_injective (fun _ => rfl) hpos hcover (high p)
        (fun a => (layers_active p a).symm) R.val ⟨s(i,k),hik⟩
    · rw [hB i k hik,zero_smul]
      exact Submodule.zero_mem _
  obtain ⟨c,hc⟩ := hC
  let e := layerSliceEquiv (q := q) (counts := counts) R (hpos _ R.property)
  have hnew :
      (∑ k : Fin (counts R.val),layers p R.val k*rename Sum.inr (f' (e k).val).val)=
      ∑ i,if degree i=R.val then high p i*f i else 0 := by
    apply Fintype.sum_of_injective (fun k => (e k).val) (Subtype.val_injective.comp e.injective)
    · intro i hi
      have hne : degree i≠R.val := by
        intro heq
        exact hi ⟨e.symm ⟨i,heq⟩,congrArg Subtype.val (e.apply_symm_apply ⟨i,heq⟩)⟩
      simp only [if_neg hne]
    · intro k
      rw [if_pos (e k).property,hf']
      congr 1
      exact layers_active p ⟨R,k⟩
  let u' : PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) R.val :=
    fun i => ⟨u i,hu' i⟩
  have hz := hsep ((fun i => ⟨x i,hx' i⟩,fun k => f' (e k).val),c) u' (by
    simp only [row,bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,
      fullBiformScalarProduct_apply,privateRowMap,u']
    have hnew' (i) : (intrinsicLayerMap hO R i p).val=layers p R.val i := layerMap_apply _ _ _
    simp only [hnew']
    rw [show (∑ k,rename Sum.inr (f' (e k).val).val*layers p R.val k)=
      ∑ k,layers p R.val k*rename Sum.inr (f' (e k).val).val by
        apply Finset.sum_congr rfl; intro k _; exact mul_comm _ _]
    rw [hnew,hc]
    exact hrel)
  funext i
  exact congrArg Subtype.val (congrFun hz i)

end Froberg.PreparedParameters
