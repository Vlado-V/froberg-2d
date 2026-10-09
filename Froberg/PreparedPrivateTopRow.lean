module

public import Froberg.PreparedProductBiform
public import Froberg.PreparedPrivateRowOpen

@[expose] public section

/-! At output degree d+1, the private coefficients have scalar degree zero.
Their private powers separate them from every core product; this condition
then persists on the same unrestricted prepared coefficient space. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PrivateColumns Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z n d q b hi ho : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def privateTopRow (p : Space n d q J counts O)
    (P : Fin b → MvPolynomial (σ ⊕ Fin n) K) :=
  addRow (ProductRows.multiplication counts (layers p) J (d+1)) (privateRowMap (d := d) P (d+1))

theorem private_top_core_injective
    (hd : 3≤d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d)
    (bi : Basis (Fin hi) K (homogeneousSubmodule σ K d))
    (bo : Basis (Fin ho) K (homogeneousSubmodule σ K (d+1)))
    (l : Fin b → homogeneousSubmodule σ K 1) (hl : ∀ i,l i≠0)
    (ι : Fin b ↪ Fin z) (p₀ : Space a d q J counts O)
    (hprod : Function.Injective (ProductRows.multiplication counts (layers p₀) J (d+1))) :
    Function.Injective (privateTopRow (coreExtension z p₀)
      (fun i => rename Sum.inl (l i).val*
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  rintro ⟨x,u⟩ hxu
  have hrel := LinearMap.mem_ker.mp hxu
  simp only [privateTopRow,addRow,LinearMap.add_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply,privateRowMap,LinearMap.coe_mk,AddHom.coe_mk] at hrel
  have hprod' := LinearMap.congr_fun (coreExtension_products (z := z) p₀ (d+1)) x
  simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply] at hprod'
  rw [hprod'] at hrel
  let C := ProductRows.multiplication counts (layers p₀) J (d+1) x
  have hC : C∈FullBiform K σ a (d+1) (d-1) := by
    have hh := ProductRows.multiplication_range_full_biform (layers p₀) (by omega : d+1≤2*d)
      (fun j hj i => (homogeneousLayerMap hO hJ j i p₀).property)
      (fun j hj i => biformImage_output_weight _ _ (hO j hj) (by
        simpa only [layers,dif_pos hj] using (p₀.2 ⟨j,hj⟩ i).property))
    have hc := hh (show C∈(ProductRows.multiplication counts (layers p₀) J (d+1)).range from ⟨x,rfl⟩)
    simpa only [show 2*d-(d+1)=d-1 by omega] using hc
  have hu := private_biform_core_zero (s := d-1) (r := 0) (by omega) (by omega)
    bi bo l hl ι C hC (fun i => (u i).val) (by
      intro i
      simpa only [Nat.add_sub_cancel,Nat.sub_self] using (u i).property) hrel
  have hu' : u=0 := by funext i; exact Subtype.ext (congrFun hu i)
  have hx : x=0 := by
    apply hprod
    rw [map_zero]
    apply (rename_injective (Sum.map id (Fin.castAdd z))
      (Function.Injective.sumMap (fun _ _ h => h) (Fin.castAdd_injective a z)))
    simpa only [hu',Pi.zero_apply,ZeroMemClass.coe_zero,mul_zero,
      Finset.sum_const_zero,add_zero,map_zero] using hrel
  exact Prod.ext hx hu'

theorem private_top_principal_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (p₀ : Space n d q J counts O) (hp₀ : Function.Injective (privateTopRow p₀ P)) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → Function.Injective (privateTopRow p P) := by
  let e := (Module.finBasis K (Space n d q J counts O)).equivFun
  have hp := product_polynomial (n := n) (d := d) (q := q) (J := J) (counts := counts) hO hJ (d+1)
  have hpoly : IsPolynomialFamily (fun a => privateTopRow (e.symm a) P) := by
    apply isPolynomialFamily_linearMap
    intro x
    exact (hp.linear_comp (LinearMap.applyₗ (R := K) (M₂ := MvPolynomial (σ ⊕ Fin n) K) x.1)).add
      (isPolynomialFamily_const (privateRowMap (d := d) P (d+1) x.2))
  obtain ⟨D,hD,hgood⟩ := rank_polynomial_general_open (fun a => privateTopRow (e.symm a) P) hpoly (e p₀)
  refine ⟨D,hD,?_⟩
  intro p hp
  have hh := hgood (e p) hp
  have hleft := congrArg (fun x : Space n d q J counts O => finrank K (privateTopRow x P).range) (e.symm_apply_apply p₀)
  have hright := congrArg (fun x : Space n d q J counts O => finrank K (privateTopRow x P).range) (e.symm_apply_apply p)
  have hh' : finrank K (privateTopRow p₀ P).range ≤ finrank K (privateTopRow p P).range :=
    hleft ▸ hright ▸ hh
  rw [LinearMap.finrank_range_of_inj hp₀] at hh'
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have hdim := LinearMap.finrank_range_add_finrank_ker (privateTopRow p P)
  omega

end Froberg.PreparedParameters
