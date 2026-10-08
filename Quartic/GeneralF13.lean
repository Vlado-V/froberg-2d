import Quartic.ConvolutionF13
import Quartic.MiddleCoordinates

/-!
# The actual F₁₃ map for arbitrary mixed and child generators

All coefficient spaces are fixed. Only the actual homogeneous generators
vary. The reduced map and its rank criterion are proved from polynomial
multiplication and the ordinary quadratic/cubic quotient spaces.
-/
noncomputable section
namespace Quartic.GeneralF13
open Module MvPolynomial
variable {K : Type*} [Field K] {m c q : ℕ}

abbrev Mixed (K : Type*) [Field K] (m c : ℕ) := Fin c → Fin 3 → Forms K m 1
abbrev Quadrics (K : Type*) [Field K] (m q : ℕ) := Fin q → Forms K m 2
abbrev CoefficientSource (K : Type*) [Field K] (m c : ℕ) := Fin c → Forms K m 2
abbrev CubicSource (K : Type*) [Field K] (m q : ℕ) := Fin q → Fin 3 → Forms K m 1
abbrev Ambient (K : Type*) [Field K] (m : ℕ) := Fin 3 → Forms K m 3
abbrev QuadraticQuotient (Q : Quadrics K m q) := Forms K m 2 ⧸ Submodule.span K (Set.range Q)
abbrev Source (Q : Quadrics K m q) (c : ℕ) := Fin c → QuadraticQuotient Q
abbrev Target (Q : Quadrics K m q) := Fin 3 → CubicGeneric.CubicQuotient Q

/-- The original mixed columns acting on quadratic coefficients. -/
def multiplication (E : Mixed K m c) : CoefficientSource K m c →ₗ[K] Ambient K m where
  toFun u r := ∑ k, CubicGeneric.mulLinearQuad (E k r) (u k)
  map_add' u v := by funext r; simp [map_add, Finset.sum_add_distrib]
  map_smul' s u := by funext r; simp [map_smul, Finset.smul_sum]

@[simp] theorem multiplication_val (E : Mixed K m c) (u : CoefficientSource K m c) (r : Fin 3) :
    (multiplication E u r).val = ∑ k, (E k r).val * (u k).val := by
  simp [multiplication]

/-- Three independent copies of ordinary cubic multiplication by the same child quadrics. -/
def childMultiplication (Q : Quadrics K m q) : CubicSource K m q →ₗ[K] Ambient K m :=
  ConvolutionF13Square.rowwise 3 (CubicGeneric.cubicMap Q)

/-- The combined actual map on fixed spaces. -/
def combined (E : Mixed K m c) (Q : Quadrics K m q) :
    CoefficientSource K m c × CubicSource K m q →ₗ[K] Ambient K m :=
  (multiplication E).coprod (childMultiplication Q)

/-- Actual coordinatewise quadratic quotient projection. -/
def sourceProjection (Q : Quadrics K m q) : CoefficientSource K m c →ₗ[K] Source Q c :=
  LinearMap.pi fun k => (Submodule.span K (Set.range Q)).mkQ.comp (LinearMap.proj k)

/-- Actual coordinatewise cubic quotient projection. -/
def targetProjection (Q : Quadrics K m q) : Ambient K m →ₗ[K] Target Q :=
  LinearMap.pi fun r => (CubicGeneric.quadraticLinearProducts Q).mkQ.comp (LinearMap.proj r)

/-- The top quotient relations, one copy of span Q in each mixed column. -/
def sourceRelations (Q : Quadrics K m q) (c : ℕ) : Submodule K (CoefficientSource K m c) :=
  Submodule.pi Set.univ (fun _ => Submodule.span K (Set.range Q))

/-- The polynomial mixed map descends to the ordinary child quotients. -/
theorem sourceRelations_le_kernel (E : Mixed K m c) (Q : Quadrics K m q) :
    sourceRelations Q c ≤ LinearMap.ker ((targetProjection Q).comp (multiplication E)) := by
  classical
  intro u hu
  funext r
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (∑ k, CubicGeneric.mulLinearQuad (E k r) (u k)) ∈ _
  apply Submodule.sum_mem
  intro k _
  have hk := hu k (Set.mem_univ k)
  obtain ⟨s,hs⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hk
  rw [← CubicGeneric.cubicMap_range]
  refine ⟨fun j => s j • E k r, ?_⟩
  apply Subtype.ext
  simp only [CubicGeneric.cubicMap_val, SetLike.val_smul, smul_eq_C_mul,
    CubicGeneric.mulLinearQuad_val, ← hs, AddSubmonoidClass.coe_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- F₁₃ on ordinary quotient coordinates, for arbitrary actual mixed columns. -/
def f13Map (E : Mixed K m c) (Q : Quadrics K m q) : Source Q c →ₗ[K] Target Q :=
  ((sourceRelations Q c).liftQ ((targetProjection Q).comp (multiplication E))
    (sourceRelations_le_kernel E Q)).comp (Submodule.quotientPi _).symm.toLinearMap

/-- The actual quotient map commutes with the original polynomial map. -/
theorem f13Map_sourceProjection (E : Mixed K m c) (Q : Quadrics K m q)
    (u : CoefficientSource K m c) :
    f13Map E Q (sourceProjection Q u) = targetProjection Q (multiplication E u) := by
  change (sourceRelations Q c).liftQ _ (sourceRelations_le_kernel E Q)
    ((Submodule.quotientPi _).symm _) = _
  have h : (Submodule.quotientPi (fun _ : Fin c => Submodule.span K (Set.range Q)))
      (Submodule.Quotient.mk u) = sourceProjection Q u := rfl
  rw [← h, LinearEquiv.symm_apply_apply]
  rfl

/-- Every ordinary quotient tuple admits simultaneous polynomial representatives. -/
theorem sourceProjection_surjective (Q : Quadrics K m q) :
    Function.Surjective (sourceProjection (c := c) Q) := by
  classical
  intro x
  have h : ∀ k, ∃ u : Forms K m 2, (Submodule.span K (Set.range Q)).mkQ u = x k :=
    fun k => Submodule.mkQ_surjective _ (x k)
  choose u hu using h
  exact ⟨u, funext hu⟩

/-- The child image is exactly the kernel of the ordinary cubic quotient projection. -/
theorem targetProjection_kernel (Q : Quadrics K m q) :
    LinearMap.ker (targetProjection Q) = LinearMap.range (childMultiplication Q) := by
  rw [childMultiplication, ConvolutionF13.range_rows, CubicGeneric.cubicMap_range]
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  change (fun r => (CubicGeneric.quadraticLinearProducts Q).mkQ (v r)) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- The reduced map has exactly the projected mixed image. -/
theorem f13Map_range (E : Mixed K m c) (Q : Quadrics K m q) :
    LinearMap.range (f13Map E Q) = LinearMap.range ((targetProjection Q).comp (multiplication E)) := by
  have h : (f13Map E Q).comp (sourceProjection Q) =
      (targetProjection Q).comp (multiplication E) := LinearMap.ext (f13Map_sourceProjection E Q)
  rw [← h, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (sourceProjection_surjective Q))]

section RankAlgebra
variable {U V W X : Type*} [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X] [FiniteDimensional K W]

/-- Fixed-space rank formula for projection by an exactly known image. -/
theorem projected_rank_add (F : U →ₗ[K] W) (G : V →ₗ[K] W) (P : W →ₗ[K] X)
    (hker : LinearMap.ker P = LinearMap.range G) :
    finrank K (LinearMap.range (P.comp F)) + finrank K (LinearMap.range G) =
      finrank K (LinearMap.range (F.coprod G)) := by
  let S := LinearMap.range (F.coprod G)
  have hle : LinearMap.ker P ≤ S := by
    change LinearMap.ker P ≤ LinearMap.range (F.coprod G)
    rw [hker, LinearMap.range_coprod]
    exact le_sup_right
  have hr : LinearMap.range (P.comp S.subtype) = LinearMap.range (P.comp F) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    change (LinearMap.range (F.coprod G)).map P = _
    have hz : (LinearMap.ker P).map P = ⊥ := by
      apply eq_bot_iff.mpr
      rintro x ⟨y,hy,rfl⟩
      exact hy
    rw [LinearMap.range_coprod, Submodule.map_sup, ← hker, hz, sup_bot_eq, LinearMap.range_comp]
  have hk : finrank K (LinearMap.ker (P.comp S.subtype)) = finrank K (LinearMap.range G) := by
    rw [LinearMap.ker_comp]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.trans (congrArg (fun S : Submodule K W => finrank K S) hker)
  have h := LinearMap.finrank_range_add_finrank_ker (P.comp S.subtype)
  rw [hr, hk] at h
  exact h
end RankAlgebra

/-- The combined fixed-space rank is the sum of the reduced rank and the child cubic rank. -/
theorem combined_rank (E : Mixed K m c) (Q : Quadrics K m q) :
    finrank K (LinearMap.range (f13Map E Q)) + finrank K (LinearMap.range (childMultiplication Q)) =
      finrank K (LinearMap.range (combined E Q)) := by
  rw [f13Map_range]
  exact projected_rank_add _ _ _ (targetProjection_kernel Q)

/-- Independent child cubic products remain independent in all three output rows. -/
theorem childMultiplication_injective (Q : Quadrics K m q)
    (hQ : Function.Injective (CubicGeneric.cubicMap Q)) : Function.Injective (childMultiplication Q) := by
  intro v z hvz
  funext j r
  have h := hQ (congrFun hvz r)
  exact congrFun h j

/-- The actual cubic child image has dimension 3mq on its injective locus. -/
theorem childMultiplication_finrank (Q : Quadrics K m q)
    (hQ : Function.Injective (CubicGeneric.cubicMap Q)) :
    finrank K (LinearMap.range (childMultiplication Q)) = 3*m*q := by
  rw [LinearMap.finrank_range_of_inj (childMultiplication_injective Q hQ)]
  have h : finrank K (CubicSource K m q) = q*(3*m) := by
    simp [CubicSource, Module.finrank_pi_fintype, Quartic.finrank_forms]
  rw [h]
  ring

/-- The actual source dimension on the independent-quadrics locus. -/
theorem source_finrank (Q : Quadrics K m q) (hQ : LinearIndependent K Q) :
    finrank K (Source Q c) = c*((m+1).choose 2-q) := by
  have h : finrank K (QuadraticQuotient Q) = (m+1).choose 2-q := by
    rw [Submodule.finrank_quotient, finrank_span_eq_card hQ, Fintype.card_fin]
    simp [Quartic.finrank_forms]
  calc
    _ = ∑ k : Fin c, finrank K (QuadraticQuotient Q) := Module.finrank_pi_fintype K
    _ = _ := by simp [h]

/-- Injectivity of actual F₁₃ is equivalent to a rank inequality on one fixed-space map. -/
theorem injective_iff_combined_rank (E : Mixed K m c) (Q : Quadrics K m q)
    (hQ : LinearIndependent K Q) (hC : Function.Injective (CubicGeneric.cubicMap Q)) :
    Function.Injective (f13Map E Q) ↔
      c*((m+1).choose 2-q)+3*m*q ≤ finrank K (LinearMap.range (combined E Q)) := by
  have h := combined_rank E Q
  rw [childMultiplication_finrank Q hC] at h
  have hn := LinearMap.finrank_range_add_finrank_ker (f13Map E Q)
  rw [source_finrank Q hQ] at hn
  constructor
  · intro hi
    rw [LinearMap.finrank_range_of_inj hi, source_finrank Q hQ] at h
    omega
  · intro hr
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    omega

end Quartic.GeneralF13
