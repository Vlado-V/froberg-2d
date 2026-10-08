import Froberg.PreparedWitnessEmbedding
import Froberg.PreparedFiniteRows
import Froberg.PreparedEvenReduction

/-! Above the coefficient degree the prepared-family condition is just
independence of actual products; it is open in the same common parameters. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

/-- A product witness gives a principal open in the full common parameter
space, including the scalar coordinates. -/
theorem product_principal_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : ℕ) (p₀ : Space n d q J counts O)
    (hp₀ : Function.Injective (ProductRows.multiplication counts (layers p₀) J R)) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  let e := (Module.finBasis K (Space n d q J counts O)).equivFun
  letI : Module.Finite K (homogeneousSubmodule (σ ⊕ Fin n) K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis (σ ⊕ Fin n) d)
  have hsame (p : Space n d q J counts O) :
      (fun j i => (homogeneousLayerMap (q := q) hO hJ j i p).val)=layers p := by
    funext j i
    exact layerMap_apply j i _
  obtain ⟨D,hD,hgood⟩ := ProductRows.product_row_principal_open counts
    (homogeneousSubmodule (σ ⊕ Fin n) K d).subtype
    (fun j i a => homogeneousLayerMap (q := q) hO hJ j i (e.symm a)) J R
    (fun j _ i => isPolynomialFamily_linear
      ((homogeneousLayerMap (q := q) hO hJ j i).comp e.symm.toLinearMap))
    (e p₀) (by simpa only [Submodule.subtype_apply,hsame,LinearEquiv.symm_apply_apply] using hp₀)
  refine ⟨D,hD,?_⟩
  intro p hp
  simpa only [Submodule.subtype_apply,hsame,LinearEquiv.symm_apply_apply] using hgood (e p) hp

/-- All product rows can be imposed on one nonempty principal open. -/
theorem products_common_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (T : Finset ℕ)
    (hwitness : ∀ R∈T,∃ p : Space n d q J counts O,
      Function.Injective (ProductRows.multiplication counts (layers p) J R)) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ R∈T,Function.Injective (ProductRows.multiplication counts (layers p) J R) := by
  classical
  choose p hp using fun R : T => hwitness R.val R.property
  choose D hD hgood using fun R : T => product_principal_open hO hJ R.val (p R) (hp R)
  have hnz (R : T) : D R≠0 := by
    intro hz
    exact hD R (by rw [hz,map_zero])
  obtain ⟨a,ha⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ R,D R,⟨(Module.finBasis K _).equivFun.symm a,?_⟩,?_⟩
  · simp only [LinearEquiv.apply_symm_apply,map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun R _ => ha R)
  intro p hp R hR
  rw [map_prod] at hp
  exact hgood ⟨R,hR⟩ p (Finset.prod_ne_zero_iff.mp hp ⟨R,hR⟩ (Finset.mem_univ _))

end Froberg.PreparedParameters
