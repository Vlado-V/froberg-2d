module

public import Froberg.PreparedPrivateRowOpen
public import Froberg.GeneralComplexOpen

@[expose] public section

/-! The first private-private constants and later zero private boundaries
are handled uniformly by exactness on the same prepared coefficient space. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}
variable {B : Type*} [AddCommGroup B] [Module K B] [FiniteDimensional K B]

 theorem private_boundary_row_principal_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : J) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (Z : B →ₗ[K] PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) R.val)
    (hPZ : (privateRowMap (d := d) P R.val).comp Z=0)
    (p₀ : Space n d q J counts O)
    (hexact : (privateAugmentedRow hO R p₀ P).ker=
      ((rowConstants hO R p₀).prodMap Z).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        (privateAugmentedRow hO R p P).ker=((rowConstants hO R p).prodMap Z).range := by
  let e := (Module.finBasis K (Space n d q J counts O)).equivFun
  have hrow : IsPolynomialFamily (fun a => row hO R (e.symm a)) :=
    bilinearKoszulRow_polynomial fullBiformScalarProduct
      (fun i a => scalarMap i (e.symm a)) (fun i a => intrinsicLayerMap hO R i (e.symm a))
      (fun a => ProductRows.multiplication counts (layers (e.symm a)) J R.val)
      (fun i => isPolynomialFamily_linear ((scalarMap i).comp e.symm.toLinearMap))
      (fun i => isPolynomialFamily_linear ((intrinsicLayerMap hO R i).comp e.symm.toLinearMap))
      (product_polynomial hO hJ R.val)
  have hconstants : IsPolynomialFamily (fun a => rowConstants hO R (e.symm a)) :=
    bilinearKoszulConstants_polynomial
      (fun i a => scalarMap i (e.symm a)) (fun i a => intrinsicLayerMap hO R i (e.symm a))
      (fun i => isPolynomialFamily_linear ((scalarMap i).comp e.symm.toLinearMap))
      (fun i => isPolynomialFamily_linear ((intrinsicLayerMap hO R i).comp e.symm.toLinearMap))
  have hA : IsPolynomialFamily (fun a => privateAugmentedRow hO R (e.symm a) P) := by
    apply isPolynomialFamily_linearMap
    intro x
    exact (hrow.linear_comp (LinearMap.applyₗ (R := K) (M₂ := MvPolynomial (σ ⊕ Fin n) K) x.1)).add
      (isPolynomialFamily_const (privateRowMap (d := d) P R.val x.2))
  have hC : IsPolynomialFamily (fun a => (rowConstants hO R (e.symm a)).prodMap Z) := by
    apply isPolynomialFamily_linearMap
    intro C
    exact (hconstants.linear_comp (LinearMap.applyₗ (R := K) C.1)).prod_mk (isPolynomialFamily_const (Z C.2))
  have hcomp : ∀ a,(privateAugmentedRow hO R (e.symm a) P).comp
      ((rowConstants hO R (e.symm a)).prodMap Z)=0 := by
    intro a
    apply LinearMap.ext
    rintro ⟨C,z⟩
    change row hO R (e.symm a) (rowConstants hO R (e.symm a) C)+privateRowMap (d := d) P R.val (Z z)=0
    have hz : privateRowMap (d := d) P R.val (Z z)=0 := LinearMap.congr_fun hPZ z
    rw [hz,add_zero]
    exact LinearMap.congr_fun (bilinearKoszulRow_constants fullBiformScalarProduct _ _ _) C
  obtain ⟨D,hD,hgood⟩ := complex_general_exact_principal_open
    (fun a => privateAugmentedRow hO R (e.symm a) P)
    (fun a => (rowConstants hO R (e.symm a)).prodMap Z) hA hC hcomp (e p₀)
    (by rw [e.symm_apply_apply];exact hexact)
  refine ⟨D,hD,?_⟩
  intro p hp
  have hh := hgood (e p) hp
  rw [e.symm_apply_apply] at hh
  exact hh

end Froberg.PreparedParameters
