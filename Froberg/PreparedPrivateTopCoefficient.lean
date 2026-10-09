module

public import Froberg.PreparedPrivateTopRow
public import Froberg.PreparedCoefficientRows

@[expose] public section

/-! The stable top-row injectivity condition gives literal private
coefficient separation at output degree d+1. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_top_coefficient_separation
    (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j)
    (p : Space n d q J counts O) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (htop : Function.Injective (privateTopRow p P)) :
    PrivateRowSeparation
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (scalar p) (high p) P degree (d+1) := by
  classical
  intro x f B u hx hf hu hB hrel
  have hdeg (i : Label q J counts) : degree i≤d := by
    cases i with
    | inl i => exact Nat.zero_le _
    | inr i => exact hJ _ i.1.property
  have hx0 (i) : x i=0 := by
    have hi := hx i
    rw [coefficientComponentSpace_above _ (by intro i; cases i <;> simp) (by omega : d<d+1)] at hi
    exact hi
  have hne (i : Label q J counts) : degree i≠d+1 := by have := hdeg i; omega
  have hu' (i) : u i∈FullBiform K σ n d 0 := by
    apply mem_biformImage_of_homogeneous
    · simpa only [Nat.add_zero] using (show (u i).IsHomogeneous d from (hu i).1)
    · simpa only [Nat.add_sub_cancel] using
        (show (u i).IsWeightedHomogeneous (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) (d+1-1) from (hu i).2)
  let C := ∑ i,∑ k,B i k • (high p i*high p k)
  have hcover (i : Label q J counts) (hi : 0<degree i) :
      ∃ a : ProductRows.LayerLabel J counts,Sum.inr a=i := by
    cases i with
    | inl i => exact False.elim (by change 0<0 at hi; omega)
    | inr a => exact ⟨a,rfl⟩
  have hC : C∈(ProductRows.multiplication counts (layers p) J (d+1)).range := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro k _
    by_cases hik : 0<degree i ∧ 0<degree k ∧ degree i+degree k=d+1
    · apply Submodule.smul_mem
      exact ProductRows.prepared_pair_mem_product_range (layers p) degree Sum.inr
        Sum.inr_injective (fun _ => rfl) hpos hcover (high p)
        (fun a => (layers_active p a).symm) (d+1) ⟨s(i,k),hik⟩
    · rw [hB i k hik,zero_smul]
      exact Submodule.zero_mem _
  obtain ⟨c,hc⟩ := hC
  let u' : PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) (d+1) :=
    fun i => ⟨u i,by simpa only [Nat.add_sub_cancel,Nat.sub_self] using hu' i⟩
  have hz : privateTopRow p P (c,u')=privateTopRow p P 0 := by
    rw [map_zero]
    simp only [privateTopRow,addRow,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.fst_apply,LinearMap.snd_apply,LinearMap.coe_mk,AddHom.coe_mk,privateRowMap,u',hc]
    simpa only [hx0,mul_zero,Finset.sum_const_zero,zero_add,if_neg (hne _)] using hrel
  have hh := congrArg Prod.snd (htop hz)
  funext i
  exact congrArg Subtype.val (congrFun hh i)

end Froberg.PreparedParameters
