module

public import Froberg.PreparedRowOpen
public import Froberg.PrivateCoefficientRow

@[expose] public section

/-! The ordinary and private coefficient blocks share one actual prepared
parameter space. Exactness of their combined row is a principal-open property. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]

 theorem addRow_exact_of_separated
    {A B U V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (F : A →ₗ[K] V) (P : B →ₗ[K] V) (C : U →ₗ[K] A)
    (hexact : F.ker=C.range)
    (hsep : ∀ a b,F a+P b=0 → b=0) :
    (addRow F P).ker=((LinearMap.inl K A B).comp C).range := by
  apply le_antisymm
  · rintro ⟨a,b⟩ hab
    have hb := hsep a b hab
    subst b
    have ha : a∈F.ker := by
      change F a=0
      change F a+P 0=0 at hab
      simpa only [map_zero,add_zero] using hab
    rw [hexact] at ha
    obtain ⟨c,rfl⟩ := ha
    exact ⟨c,rfl⟩
  · rintro _ ⟨c,rfl⟩
    have hc : C c∈F.ker := hexact.ge ⟨c,rfl⟩
    change F (C c)+P 0=0
    change F (C c)=0 at hc
    simpa only [map_zero,add_zero] using hc

namespace PreparedParameters
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

abbrev IntrinsicRowSource (R : ℕ) :=
  ((Label q J counts → FullBiform K σ n R (d-R)) × (Fin (counts R) → Forms K n d)) ×
    RowProducts (K := K) (J := J) (counts := counts) R

abbrev PrivateRowSource (R : ℕ) := Fin b → FullBiform K σ n (R-1) (d-(R-1))

def privateRowMap (P : Fin b → MvPolynomial (σ ⊕ Fin n) K) (R : ℕ) :
    PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) R →ₗ[K]
      MvPolynomial (σ ⊕ Fin n) K where
  toFun v := ∑ i,P i*(v i).val
  map_add' v w := by simp only [Pi.add_apply,Submodule.coe_add,mul_add,Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply,Submodule.coe_smul,mul_smul_comm,Finset.smul_sum,RingHom.id_apply]

def privateAugmentedRow (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K) :=
  addRow (row hO R p) (privateRowMap (d := d) P R.val)

def privateAugmentedConstants (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O) :=
  (LinearMap.inl K (IntrinsicRowSource (K := K) (σ := σ) (n := n) (d := d) (q := q) (J := J) (counts := counts) R.val)
    (PrivateRowSource (K := K) (σ := σ) (n := n) (d := d) (b := b) R.val)).comp (rowConstants hO R p)

 theorem private_augmented_exact
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hrow : (row hO R p).ker=(rowConstants hO R p).range)
    (hsep : ∀ x v,row hO R p x+privateRowMap (d := d) P R.val v=0 → v=0) :
    (privateAugmentedRow hO R p P).ker=(privateAugmentedConstants (b := b) hO R p).range :=
  addRow_exact_of_separated _ _ _ hrow hsep

 theorem private_row_principal_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : J) (P : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (p₀ : Space n d q J counts O)
    (hE : LinearIndependent K (fun i => intrinsicLayerMap hO R i p₀))
    (hexact : (privateAugmentedRow hO R p₀ P).ker=
      (privateAugmentedConstants (b := b) hO R p₀).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        (privateAugmentedRow hO R p P).ker=(privateAugmentedConstants (b := b) hO R p).range := by
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
  have hC : IsPolynomialFamily (fun a => privateAugmentedConstants (b := b) hO R (e.symm a)) := by
    apply isPolynomialFamily_linearMap
    intro C
    exact (hconstants.linear_comp (LinearMap.applyₗ (R := K) C)).prod_mk (isPolynomialFamily_const 0)
  have hcomp : ∀ a,(privateAugmentedRow hO R (e.symm a) P).comp
      (privateAugmentedConstants (b := b) hO R (e.symm a))=0 := by
    intro a
    apply LinearMap.ext
    intro C
    change row hO R (e.symm a) (rowConstants hO R (e.symm a) C)+privateRowMap (d := d) P R.val 0=0
    rw [map_zero,add_zero]
    exact LinearMap.congr_fun (bilinearKoszulRow_constants fullBiformScalarProduct _ _ _) C
  have hCI : Function.Injective (privateAugmentedConstants (b := b) hO R p₀) := by
    intro C D h
    apply bilinearKoszulConstants_injective
      (W := RowProducts (K := K) (J := J) (counts := counts) R.val)
      (fun i => scalarMap i p₀) (fun i => intrinsicLayerMap hO R i p₀) hE
    exact congrArg Prod.fst h
  obtain ⟨D,hD,hgood⟩ := exact_kernel_general_open
    (fun a => privateAugmentedRow hO R (e.symm a) P)
    (fun a => privateAugmentedConstants (b := b) hO R (e.symm a))
    hA hC hcomp (e p₀)
    (by rw [e.symm_apply_apply]; exact hCI)
    (by rw [e.symm_apply_apply]; exact hexact)
  refine ⟨D,hD,?_⟩
  intro p hp
  have hh := (hgood (e p) hp).2
  rw [e.symm_apply_apply] at hh
  exact hh

end PreparedParameters
end Froberg
