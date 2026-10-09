module

public import Quartic.CubicCoordinateProducts
public import Quartic.CubicInequality
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-!
# Exact dimension of cubic products of arbitrary linear forms

For an arbitrary subspace `D` of the actual linear forms in `m` variables,
its products with all quadrics have dimension
`choose (m + 2) 3 - choose (m - finrank D + 2) 3`.

The proof chooses a complement, proves the induced polynomial change of
basis, and transports the exact coordinate projection computation. No
higher-degree rank premise is assumed.
-/

noncomputable section
namespace Quartic.CubicProductDimension
open MvPolynomial Module CubicLinearCoordinates CubicCoordinateProducts
variable {K σ ι τ : Type*} [Field K]

/-- Cubics obtained by multiplying a member of `D` by an arbitrary quadric. -/
def cubicProducts (D : Submodule K (H K σ 1)) : Submodule K (H K σ 3) :=
  products (D.map (H K σ 1).subtype)

private theorem finrank_products_ambient (D : Submodule K (MvPolynomial σ K))
    (hD : D ≤ H K σ 1) : finrank K (products D) = finrank K (D * H K σ 2) := by
  have he : (products D).map (H K σ 3).subtype = D * H K σ 2 := by
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_subtype]
    exact (mul_le_mul_left hD _).trans (homogeneousSubmodule_mul 1 2)
  rw [← he, Submodule.finrank_map_subtype_eq]

private theorem finrank_products_change_basis (b : Basis ι K (H K σ 1))
    (D : Submodule K (MvPolynomial ι K)) (hD : D ≤ H K ι 1) :
    finrank K (products (D.map (polynomialEquiv b).toLinearMap)) =
      finrank K (products D) := by
  have hmap : D.map (polynomialEquiv b).toLinearMap ≤ H K σ 1 := by
    rw [← map_homogeneous b 1]
    exact Submodule.map_mono hD
  rw [finrank_products_ambient _ hmap, finrank_products_ambient _ hD]
  have hmul : (D * H K ι 2).map (polynomialEquiv b).toLinearMap =
      D.map (polynomialEquiv b).toLinearMap * H K σ 2 := by
    calc
      _ = D.map (polynomialEquiv b).toLinearMap *
          (H K ι 2).map (polynomialEquiv b).toLinearMap :=
        Submodule.map_mul D (H K ι 2) (polynomialEquiv b).toAlgHom
      _ = _ := by rw [map_homogeneous]
  rw [← hmul]
  exact (polynomialEquiv b).toLinearEquiv.finrank_map_eq _

private theorem span_basis_values {V J : Type*} [AddCommGroup V] [Module K V]
    (D : Submodule K V) (b : Basis J K D) :
    Submodule.span K (Set.range (fun i => (b i).val)) = D := by
  change Submodule.span K (Set.range (D.subtype ∘ b)) = D
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, D.range_subtype]

private def submoduleBasis {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (D : Submodule K V) : Basis (Fin (finrank K D)) K D :=
  Module.finBasis K D

/-- The exact cubic image dimension, for every linear subspace and every field. -/
theorem finrank_cubicProducts (m : ℕ) (D : Submodule K (Forms K m 1)) :
    finrank K (cubicProducts D) =
      (m + 2).choose 3 - (m - finrank K D + 2).choose 3 := by
  classical
  obtain ⟨E, hE⟩ := D.exists_isCompl
  let bD := submoduleBasis D
  let bE := submoduleBasis E
  let b : Basis (Fin (finrank K D) ⊕ Fin (finrank K E)) K (Forms K m 1) :=
    (bD.prod bE).map (Submodule.prodEquivOfIsCompl D E hE)
  have hb (i : Fin (finrank K D)) : (b (Sum.inl i)).val = (bD i).val.val := by
    simp [b, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hmap : (leftSpace K (Fin (finrank K D)) (Fin (finrank K E))).map
      (polynomialEquiv b).toLinearMap = D.map (Forms K m 1).subtype := by
    rw [leftSpace, Submodule.map_span, ← Set.range_comp]
    have he : ((polynomialEquiv b).toLinearMap ∘
        (fun i : Fin (finrank K D) => (X (Sum.inl i) :
          MvPolynomial (Fin (finrank K D) ⊕ Fin (finrank K E)) K))) =
        fun i => (bD i).val.val := by
      funext i
      exact (polynomialEquiv_X b (Sum.inl i)).trans (hb i)
    rw [he]
    have hv := congrArg (fun S => S.map (Forms K m 1).subtype) (span_basis_values D bD)
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.subtype_apply] using hv
  have hdim : finrank K D + finrank K E = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hE
    simpa [Quartic.finrank_forms] using h
  have hr := finrank_products_change_basis b
    (leftSpace K (Fin (finrank K D)) (Fin (finrank K E))) leftSpace_homogeneous
  rw [hmap, finrank_coordinate_products] at hr
  simp only [Fintype.card_fin] at hr
  rw [hdim, show finrank K E = m - finrank K D by omega] at hr
  exact hr

/-- The product dimension written without truncated subtraction. -/
theorem finrank_cubicProducts_add (m : ℕ) (D : Submodule K (Forms K m 1)) :
    finrank K (cubicProducts D) + (m - finrank K D + 2).choose 3 = (m + 2).choose 3 := by
  rw [finrank_cubicProducts]
  exact Nat.sub_add_cancel (Nat.choose_le_choose 3 (by omega))

/-- The dimension bound used by the cubic incidence argument, now for the
actual polynomial product subspace rather than only a numerical expression. -/
theorem cubicProducts_incidence_bound (m q : ℕ) (D : Submodule K (Forms K m 1))
    (hm : 3 ≤ m) (hq : m * q ≤ (m + 2).choose 3) :
    finrank K D * (m + q - finrank K D) ≤ finrank K (cubicProducts D) := by
  have hd : finrank K D ≤ m := by
    have h := Submodule.finrank_le D
    simpa [Quartic.finrank_forms] using h
  have h := CubicInequality.incidence_gap_nonnegative m q (finrank K D) hm hd
    (by unfold Counts.b3; exact_mod_cast hq)
  have he := finrank_cubicProducts_add m D
  unfold CubicInequality.imageDimension Counts.b3 at h
  have heZ : (finrank K (cubicProducts D) : ℤ) +
      ((m - finrank K D + 2).choose 3 : ℤ) = ((m + 2).choose 3 : ℤ) := by
    exact_mod_cast he
  have hcast : ((m + q - finrank K D : ℕ) : ℤ) = (m : ℤ) + q - finrank K D := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  apply Int.ofNat_le.mp
  rw [Nat.cast_mul, hcast]
  omega

end Quartic.CubicProductDimension
