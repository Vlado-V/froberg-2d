import Quartic.CubicProductDimension
import Quartic.BilinearGeneric

/-!
# Generic independence of actual cubic products

Over every infinite field, `m*q ≤ choose (m+2) 3` and `m ≥ 3` give a nonempty
principal open of ordered quadratic families for which multiplication by
linear forms is injective. The coefficient ranks are computed from actual
polynomial products in `CubicProductDimension`.
-/

noncomputable section
namespace Quartic.CubicGeneric
open MvPolynomial Module CubicLinearCoordinates CubicCoordinateProducts CubicProductDimension
open PolynomialBilinearCoordinates
variable {K : Type*} [Field K] {m q : ℕ}

/-- Actual multiplication of a linear form by a quadric. -/
def mulLinearQuad : Forms K m 1 →ₗ[K] Forms K m 2 →ₗ[K] Forms K m 3 where
  toFun l :=
    { toFun := fun f => ⟨l.val * f.val, l.property.mul f.property⟩
      map_add' := fun f g => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c f => Subtype.ext (mul_smul_comm _ _ _) }
  map_add' l r := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact add_mul _ _ _
  map_smul' c l := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact smul_mul_assoc _ _ _

@[simp] theorem mulLinearQuad_val (l : Forms K m 1) (f : Forms K m 2) :
    (mulLinearQuad l f).val = l.val * f.val := rfl

/-- Vary the quadratic coefficients with a fixed tuple of linear relations. -/
def coefficientMap (L : Fin q → Forms K m 1) :
    (Fin q → Forms K m 2) →ₗ[K] Forms K m 3 :=
  ∑ i, (mulLinearQuad (L i)).comp (LinearMap.proj i)

@[simp] theorem coefficientMap_val (L : Fin q → Forms K m 1) (Q : Fin q → Forms K m 2) :
    (coefficientMap L Q).val = ∑ i, (L i).val * (Q i).val := by
  simp [coefficientMap]

/-- The actual bilinear family, linear in both relation tuples and quadrics. -/
def bilinear : (Fin q → Forms K m 1) →ₗ[K] (Fin q → Forms K m 2) →ₗ[K] Forms K m 3 where
  toFun := coefficientMap
  map_add' L R := by
    apply LinearMap.ext
    intro Q
    apply Subtype.ext
    simp [coefficientMap_val, add_mul, Finset.sum_add_distrib]
  map_smul' c L := by
    apply LinearMap.ext
    intro Q
    apply Subtype.ext
    simp [coefficientMap_val, Finset.smul_sum]

/-- Cubic multiplication by an ordered family of actual quadrics. -/
def cubicMap (Q : Fin q → Forms K m 2) :
    (Fin q → Forms K m 1) →ₗ[K] Forms K m 3 := bilinear.flip Q

@[simp] theorem cubicMap_val (Q : Fin q → Forms K m 2) (L : Fin q → Forms K m 1) :
    (cubicMap Q L).val = ∑ i, (L i).val * (Q i).val := coefficientMap_val L Q

/-- The fixed-tuple equations have the actual cubic image of their linear span. -/
theorem coefficientMap_range (L : Fin q → Forms K m 1) :
    LinearMap.range (coefficientMap L) = cubicProducts (Submodule.span K (Set.range L)) := by
  have hamb : LinearMap.range ((Forms K m 3).subtype.comp (coefficientMap L)) =
      Submodule.span K (Set.range (fun i => (L i).val)) * Forms K m 2 := by
    apply le_antisymm
    · rintro p ⟨Q, rfl⟩
      change (coefficientMap L Q).val ∈ _
      rw [coefficientMap_val]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (Q i).property
    · apply Submodule.mul_le.mpr
      intro l hl f hf
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hl
      refine ⟨fun i => c i • (⟨f, hf⟩ : Forms K m 2), ?_⟩
      change (coefficientMap L (fun i => c i • (⟨f, hf⟩ : Forms K m 2))).val = _
      simp [coefficientMap_val, Finset.sum_mul]
  have h := congrArg (fun S : Submodule K (Poly K m) => S.comap (Forms K m 3).subtype) hamb
  rw [LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)] at h
  simpa only [cubicProducts, products, Submodule.map_span, ← Set.range_comp,
    Function.comp_def, Submodule.subtype_apply] using h

/-- Exact coefficient rank, with no genericity or rank hypothesis. -/
theorem coefficientMap_finrank (L : Fin q → Forms K m 1) :
    finrank K (LinearMap.range (coefficientMap L)) =
      (m + 2).choose 3 -
        (m - finrank K (Submodule.span K (Set.range L)) + 2).choose 3 := by
  rw [coefficientMap_range, finrank_cubicProducts]

/-- Actual ranks meet the projective relation-stratum bound. -/
theorem coefficientMap_incidence_bound (hm : 3 ≤ m) (hq : m * q ≤ (m + 2).choose 3)
    (L : Fin q → Forms K m 1) :
    let d := finrank K (Submodule.span K (Set.range L))
    d * (finrank K (Forms K m 1) - d) + q * d ≤
      finrank K (LinearMap.range (coefficientMap L)) := by
  dsimp only
  rw [coefficientMap_range]
  have h := cubicProducts_incidence_bound m q (Submodule.span K (Set.range L)) hm hq
  have hd : finrank K (Submodule.span K (Set.range L)) ≤ m := by
    simpa [Quartic.finrank_forms] using Submodule.finrank_le (Submodule.span K (Set.range L))
  have he : finrank K (Forms K m 1) = m := by simp [Quartic.finrank_forms]
  rw [he]
  have heq : finrank K (Submodule.span K (Set.range L)) *
      (m - finrank K (Submodule.span K (Set.range L))) +
      q * finrank K (Submodule.span K (Set.range L)) =
      finrank K (Submodule.span K (Set.range L)) *
        (m + q - finrank K (Submodule.span K (Set.range L))) := by
    rw [show m + q - finrank K (Submodule.span K (Set.range L)) =
      (m - finrank K (Submodule.span K (Set.range L))) + q by omega]
    ring
  rwa [heq]

/-- A nonempty determinant-open set of actual quadratic families with no linear syzygies. -/
theorem generic_cubic_injective [Infinite K] (hm : 3 ≤ m)
    (hq : m * q ≤ (m + 2).choose 3) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K m 2))) K,
      (∃ Q : Fin q → Forms K m 2, eval (coordinates K (Fin q → Forms K m 2) Q) P ≠ 0) ∧
      ∀ Q, eval (coordinates K (Fin q → Forms K m 2) Q) P ≠ 0 →
        Function.Injective (cubicMap Q) := by
  exact BilinearGeneric.generic_injective_actual (bilinear (K := K) (m := m) (q := q))
    (fun L _ => coefficientMap_incidence_bound hm hq L)

/-- A concrete independent-cubic-products witness exists under the source budget. -/
theorem exists_cubic_injective [Infinite K] (hm : 3 ≤ m)
    (hq : m * q ≤ (m + 2).choose 3) :
    ∃ Q : Fin q → Forms K m 2, Function.Injective (cubicMap Q) := by
  obtain ⟨P, ⟨Q, hQ⟩, hgood⟩ := generic_cubic_injective (K := K) hm hq
  exact ⟨Q, hgood Q hQ⟩

/-- Injectivity of cubic multiplication also forces independence of the quadrics. -/
theorem quadrics_independent_of_cubic_injective (hm : 0 < m)
    (Q : Fin q → Forms K m 2) (hQ : Function.Injective (cubicMap Q)) :
    LinearIndependent K Q := by
  classical
  let j : Fin m := ⟨0, hm⟩
  let l : Forms K m 1 := ⟨X j, isHomogeneous_X K j⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hs : ∑ i, c i • (Q i).val = 0 := by
    simpa using congrArg Subtype.val hc
  have hz : cubicMap Q (fun i => c i • l) = 0 := by
    apply Subtype.ext
    rw [cubicMap_val]
    change (∑ i, (c i • l.val) * (Q i).val) = 0
    calc
      _ = l.val * ∑ i, c i • (Q i).val := by
        simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc]
      _ = 0 := by rw [hs, mul_zero]
  have he : (fun i => c i • l) = 0 := hQ (hz.trans (map_zero _).symm)
  have hi : c i • l.val = 0 := congrArg Subtype.val (congrFun he i)
  exact (smul_eq_zero.mp hi).resolve_right (X_ne_zero j)

/-- The intrinsic product subspace generated by the ordered quadrics in degree three. -/
def quadraticLinearProducts (Q : Fin q → Forms K m 2) : Submodule K (Forms K m 3) :=
  (Submodule.span K (Set.range (fun i => (Q i).val)) * Forms K m 1).comap
    (Forms K m 3).subtype

theorem cubicMap_range (Q : Fin q → Forms K m 2) :
    LinearMap.range (cubicMap Q) = quadraticLinearProducts Q := by
  have hamb : LinearMap.range ((Forms K m 3).subtype.comp (cubicMap Q)) =
      Submodule.span K (Set.range (fun i => (Q i).val)) * Forms K m 1 := by
    apply le_antisymm
    · rintro p ⟨L, rfl⟩
      change (cubicMap Q L).val ∈ _
      rw [cubicMap_val]
      apply Submodule.sum_mem
      intro i _
      rw [mul_comm (L i).val (Q i).val]
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (L i).property
    · apply Submodule.mul_le.mpr
      intro f hf l hl
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
      refine ⟨fun i => c i • (⟨l, hl⟩ : Forms K m 1), ?_⟩
      change (cubicMap Q (fun i => c i • (⟨l, hl⟩ : Forms K m 1))).val = _
      simp [cubicMap_val, Finset.mul_sum, mul_comm]
  have h := congrArg (fun S : Submodule K (Poly K m) => S.comap (Forms K m 3).subtype) hamb
  rw [LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)] at h
  exact h

/-- The actual cubic quotient by the products of the quadratic family. -/
abbrev CubicQuotient (Q : Fin q → Forms K m 2) :=
  Forms K m 3 ⧸ quadraticLinearProducts Q

theorem cubic_quotient_finrank_of_injective (Q : Fin q → Forms K m 2)
    (hQ : Function.Injective (cubicMap Q)) :
    finrank K (CubicQuotient Q) = (m + 2).choose 3 - m * q := by
  let : Module.Free K (Forms K m 1) := Module.Free.of_basis (formsBasis K m 1)
  change finrank K (Forms K m 3 ⧸ quadraticLinearProducts Q) = _
  rw [Submodule.finrank_quotient, ← cubicMap_range, LinearMap.finrank_range_of_inj hQ,
    Module.finrank_pi_fintype]
  simp [Quartic.finrank_forms, Nat.mul_comm]

/-- All conclusions of the source cubic lemma hold on one nonempty principal open. -/
theorem generic_cubic_independence [Infinite K] (hm : 3 ≤ m)
    (hq : m * q ≤ (m + 2).choose 3) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K m 2))) K,
      (∃ Q : Fin q → Forms K m 2, eval (coordinates K (Fin q → Forms K m 2) Q) P ≠ 0) ∧
      ∀ Q, eval (coordinates K (Fin q → Forms K m 2) Q) P ≠ 0 →
        LinearIndependent K Q ∧ Function.Injective (cubicMap Q) ∧
          finrank K (CubicQuotient Q) = (m + 2).choose 3 - m * q := by
  obtain ⟨P, hP, hgood⟩ := generic_cubic_injective (K := K) hm hq
  refine ⟨P, hP, fun Q hQ => ?_⟩
  have hi := hgood Q hQ
  exact ⟨quadrics_independent_of_cubic_injective (by omega) Q hi, hi,
    cubic_quotient_finrank_of_injective Q hi⟩

end Quartic.CubicGeneric
