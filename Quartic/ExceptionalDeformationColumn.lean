/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.ActualDeformationColumnsOmega
public import Quartic.ExceptionalSquareCorrection
public import Quartic.PersistentColumnRank

/-!
# An actual fourth-order column from a killed marked square

When the marked child has a cycle whose marked coefficient is the child
itself, two additional cancellations reach the middle block. This produces
a persistent column with the mixed coefficient of a preimage of the pure
square correction. All equalities concern the actual quartic multiplication.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Quartic.ExceptionalDeformationColumn
open Module MvPolynomial ActualSplitCokernel ActualDeformationColumnsOmega
open scoped TensorProduct

variable {K : Type*} [Field K] {m c q : ℕ}

private theorem targetEmbedding_neg (t : SplitBlock22.Target K m) :
    SplitBlock22.targetEmbedding (-t) = -SplitBlock22.targetEmbedding t := by
  apply eq_neg_of_add_eq_zero_left
  rw [← map_add, TensorProduct.neg_add_cancel, map_zero]

/-- The square correction, bundled as homogeneous quadratics. -/
def pureCorrection (ω : K) : Fin 4 → Forms K 3 2 :=
  ![-((ω + 1) ^ 2) • ThreeBlockModel.blockQuadrics 0,
    -(ω ^ 2) • ThreeBlockModel.blockQuadrics 1,
    -ThreeBlockModel.blockQuadrics 2,
    (ω ^ 2) • ThreeBlockQuotient.square 0 + ThreeBlockQuotient.square 1]

theorem pureCorrection_val (ω : K) (i : Fin 4) :
    (pureCorrection ω i).val = ExceptionalSquareCorrection.correction ω i := by
  fin_cases i <;>
    simp [pureCorrection, ExceptionalSquareCorrection.correction, ThreeBlockQuotient.square,
      ThreeBlock.x, ThreeBlock.y, MvPolynomial.smul_eq_C_mul]

theorem pureCorrection_square (ω : K) :
    quadraticMultiplication (ThreeBlockModel.blockQuadrics (K := K)) (pureCorrection ω) =
      mulQuadratic (markedDirection ω) (markedDirection ω) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val]
  simp only [ThreeBlockModel.blockQuadrics_val, pureCorrection_val]
  have he := ExceptionalSquareCorrection.square_identity ω
  simp only [ThreeBlock.relation] at he
  simpa [Fin.sum_univ_succ, mulQuadratic, markedDirection, ThreeBlockQuotient.square,
    MvPolynomial.smul_eq_C_mul, ThreeBlock.x, ThreeBlock.y, pow_two, mul_comm, add_assoc] using he

theorem pureCorrection_elimination (ω : K) (h : Fin q → Forms K m 2)
    (r : Fin 4 → Forms K m 2) :
    SplitBlock22.elimination (Submodule.span K (Set.range h))
      (pureFirstResponse r (pureCorrection ω)) =
      ((ω ^ 2) • (Submodule.span K (Set.range h)).mkQ (r 3),
        (Submodule.span K (Set.range h)).mkQ (r 3)) := by
  simp [pureFirstResponse, pureCorrection, Fin.sum_univ_succ,
    SplitBlock22.elimination_tmul, ThreeBlockQuotient.reduction_quadric]

/-- The second coefficient in the cancellation chain is supported on the marked slot. -/
def markedSource (k : Fin q) (s : Forms K 3 2) : Fin (4 + (c + q)) → Forms K (3 + m) 2 :=
  SplitBlock22.sourceEmbedding (0, 0, Pi.single k (-s))

theorem markedSource_split (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (k : Fin q) (s : Forms K 3 2) :
    quadraticMultiplication (SplitBlock22.fullGenerators g h) (markedSource k s) =
      -SplitBlock22.targetEmbedding (s ⊗ₜ[K] h k) := by
  classical
  rw [markedSource, SplitBlock22.full_multiplication_commutes]
  change SplitBlock22.targetEmbedding
    (SplitBlock22.pureMap 0 + (SplitBlock22.mixedMap g 0 +
      SplitBlock22.childMap h (Pi.single k (-s)))) = _
  simp only [map_zero, zero_add]
  have ht : SplitBlock22.childMap h (Pi.single k (-s)) = -(s ⊗ₜ[K] h k) := by
    simp [SplitBlock22.childMap_apply, Pi.single_apply, TensorProduct.ite_tmul,
      TensorProduct.neg_tmul]
  rw [ht]
  exact targetEmbedding_neg _

theorem markedSource_variation (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (s : Forms K 3 2) :
    quadraticMultiplication (motionFamily p r (Pi.single k s)) (markedSource k s) =
      -SplitBlock31.coreEmbed (mulQuadratic s s) := by
  classical
  apply Subtype.ext
  rw [quadraticMultiplication_val]
  simp [markedSource, motionFamily, SplitBlock22.sourceEmbedding, Fin.sum_univ_add,
    SplitBlock31.coreEmbed_val, mulQuadratic, Pi.single_apply, apply_ite]

/-- An actual child cycle with self coefficient yields a persistent fourth-order column. -/
theorem response_realized (ω : K) (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (a : (quadraticMultiplication h).ker) (ha : a.val k = h k)
    (z : Fin c → MiddleCoordinates.Mixed K m)
    (hz : MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z =
      -SplitBlock22.elimination (Submodule.span K (Set.range h))
        (pureFirstResponse r (pureCorrection ω))) :
    ∃ w : Forms K (3 + m) 4,
      (∀ ε : K, ε ≠ 0 →
        w ∈ (quadraticMultiplication
          (deformedFamily g h p r (Pi.single k (markedDirection ω)) ε)).range) ∧
      projectionRawJ g h w = (GeneralF13.combined g h).range.mkQ
        (∑ i, RowMultiplicationCoordinates.multiplication (p i) (z i)) := by
  classical
  let s := markedDirection ω
  let M₀ := quadraticMultiplication (SplitBlock22.fullGenerators g h)
  let M₁ := quadraticMultiplication (motionFamily p r (Pi.single k s))
  let a₀ := sourceEmbedding04 (c := c) a.val
  let a₁ := markedSource (m := m) (c := c) k s
  let a₂ := SplitBlock40.sourceEmbedding (m := m) (c := c) (q := q) (pureCorrection ω)
  have h₀ : M₀ a₀ = 0 := by
    dsimp only [M₀, a₀]
    rw [multiplication_sourceEmbedding04, a.property, map_zero]
  have hfirst : M₁ a₀ = SplitBlock22.targetEmbedding (s ⊗ₜ[K] h k) := by
    dsimp only [M₁, a₀]
    rw [firstVariation_child]
    congr 1
    simp [childFirstResponse, Pi.single_apply, TensorProduct.ite_tmul, ha]
  have h₁ : M₀ a₁ = -M₁ a₀ := by
    rw [hfirst]
    exact markedSource_split g h k s
  have h₂ : M₀ a₂ = -M₁ a₁ := by
    have hs : M₁ a₁ = -SplitBlock31.coreEmbed (mulQuadratic s s) :=
      markedSource_variation p r k s
    rw [hs, neg_neg]
    change quadraticMultiplication
      (SplitBlock31.generators (fun j => SplitBlock22.traceCoordinates (g j)) h)
        (SplitBlock40.sourceEmbedding (pureCorrection ω)) = _
    rw [SplitBlock40.multiplication_commutes, pureCorrection_square]
  obtain ⟨b, hb, hbm⟩ := prescribed_middle_completion g h
    (pureFirstResponse r (pureCorrection ω)) z hz
  let a₃ := SplitBlock22.sourceEmbedding b
  have h₃ : M₀ a₃ = -M₁ a₂ := by
    dsimp only [M₀, M₁, a₃, a₂]
    rw [SplitBlock22.full_multiplication_commutes, hbm, firstVariation_pure]
    exact targetEmbedding_neg _
  refine ⟨M₁ a₃, ?_, ?_⟩
  · intro ε he
    rw [deformed_multiplication]
    exact PersistentColumnRank.fourth_response_mem M₀ M₁ a₀ a₁ a₂ a₃ ε he h₀ h₁ h₂ h₃
  · change (GeneralF13.combined g h).range.mkQ
      (projection13 (quadraticMultiplication (motionFamily p r (Pi.single k s))
        (SplitBlock22.sourceEmbedding b))) = _
    rw [firstVariation_middle, hb]

end Quartic.ExceptionalDeformationColumn
