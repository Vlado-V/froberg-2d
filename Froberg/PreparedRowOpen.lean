import Froberg.PreparedParameterMaps
import Froberg.BilinearKoszulReindex

/-! Exactness of a prepared row is open in the full shared coefficient space.
The scalar and all product columns use those same actual parameters. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

abbrev RowProducts (R : ℕ) :=
  ((p : ProductRows.Row J R) × ProductRows.Columns counts p) →₀ K

/-- The actual intrinsic row, including every product column. -/
def row (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O) :=
  bilinearKoszulRow (fullBiformScalarProduct (R := R.val) (s := d-R.val))
    (fun i => scalarMap i p) (fun i => intrinsicLayerMap hO R i p)
    (ProductRows.multiplication counts (layers p) J R.val)

/-- Mandatory constants in this exact row. -/
def rowConstants (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (R : J) (p : Space n d q J counts O) :=
  bilinearKoszulConstants (K := K) (W := RowProducts (K := K) (J := J) (counts := counts) R.val)
    (fun i => scalarMap i p) (fun i => intrinsicLayerMap hO R i p)

/-- One actual witness gives a nonempty determinant open in the common family. -/
theorem row_principal_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (R : J) (p₀ : Space n d q J counts O)
    (hE : LinearIndependent K (fun i => intrinsicLayerMap hO R i p₀))
    (hexact : (row hO R p₀).ker=(rowConstants hO R p₀).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) D≠0 ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        (row hO R p).ker=(rowConstants hO R p).range := by
  let e := (Module.finBasis K (Space n d q J counts O)).equivFun
  obtain ⟨D,hD,hgood⟩ := bilinearKoszulRow_open
    (fullBiformScalarProduct (R := R.val) (s := d-R.val))
    (fun i a => scalarMap i (e.symm a))
    (fun i a => intrinsicLayerMap hO R i (e.symm a))
    (fun a => ProductRows.multiplication counts (layers (e.symm a)) J R.val)
    (fun i => isPolynomialFamily_linear ((scalarMap i).comp e.symm.toLinearMap))
    (fun i => isPolynomialFamily_linear ((intrinsicLayerMap hO R i).comp e.symm.toLinearMap))
    (product_polynomial hO hJ R.val) (e p₀)
    (by simpa only [LinearEquiv.symm_apply_apply] using hE)
    (by simpa only [row,rowConstants,LinearEquiv.symm_apply_apply] using hexact)
  refine ⟨D,hD,?_⟩
  intro p hp
  simpa only [row,rowConstants,LinearEquiv.symm_apply_apply] using hgood (e p) hp

/-- Separate row witnesses impose simultaneous exactness on a single
nonempty principal open of the actual prepared-family parameters. -/
theorem rows_common_open [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d)
    (hwitness : ∀ R : J,∃ p : Space n d q J counts O,
      LinearIndependent K (fun i => intrinsicLayerMap hO R i p) ∧
      (row hO R p).ker=(rowConstants hO R p).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
      (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        ∀ R : J,(row hO R p).ker=(rowConstants hO R p).range := by
  classical
  choose p hpE hpK using hwitness
  choose D hD hgood using fun R => row_principal_open hO hJ R (p R) (hpE R) (hpK R)
  have hnz (R : J) : D R≠0 := by
    intro hz
    exact hD R (by rw [hz,map_zero])
  obtain ⟨a,ha⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ R,D R,⟨(Module.finBasis K _).equivFun.symm a,?_⟩,?_⟩
  · simp only [LinearEquiv.apply_symm_apply,map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun R _ => ha R)
  intro p hp R
  rw [map_prod] at hp
  exact hgood R p (Finset.prod_ne_zero_iff.mp hp R (Finset.mem_univ R))

end Froberg.PreparedParameters
