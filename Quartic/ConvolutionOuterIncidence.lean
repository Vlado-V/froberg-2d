import Quartic.ConvolutionScalarImages
import Quartic.ConvolutionInitialImage

/-!
# Actual outer convolution multiplication and its coefficient ranks

The bilinear map sums quadratic multiplication of degree-one quotient classes.
For a fixed tuple of classes, varying every quadratic coefficient gives exactly
the full quadratic image of their span. Consequently the proved outer image
bounds are the coefficient-rank inequalities needed by a separate generic
bilinear incidence criterion. No generic injectivity theorem is assumed here.
-/
noncomputable section
namespace Quartic.ConvolutionOuterIncidence
open Module ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionProfileImage ProfileCertificate UniformEndpoint
variable {K : Type*} [Field K] {t w q : ℕ}

abbrev Coefficients (K : Type*) [Field K] (t w q : ℕ) := Fin q → Forms K (t + w) 2
abbrev SourceTuple (K : Type*) [Field K] (t w q : ℕ) := Fin q → Piece K t w 1

/-- The actual outer multiplication map for an ordered tuple of quadratic coefficients. -/
def outerMap (Q : Coefficients K t w q) : SourceTuple K t w q →ₗ[K] Piece K t w 3 :=
  ∑ i, (pieceMul (Q i)).comp (LinearMap.proj i)

@[simp] theorem outerMap_apply (Q : Coefficients K t w q) (L : SourceTuple K t w q) :
    outerMap Q L = ∑ i, pieceMul (Q i) (L i) := by
  simp [outerMap]

/-- The outer map is bilinear in the actual quadrics and quotient classes. -/
def bilinear : Coefficients K t w q →ₗ[K] SourceTuple K t w q →ₗ[K] Piece K t w 3 where
  toFun := outerMap
  map_add' Q R := by
    apply LinearMap.ext
    intro L
    simp only [outerMap_apply, LinearMap.add_apply]
    change (∑ i, ConvolutionInitialImage.pieceBilinear (Q i + R i) (L i)) = _
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    rfl
  map_smul' s Q := by
    apply LinearMap.ext
    intro L
    simp only [outerMap_apply, LinearMap.smul_apply]
    change (∑ i, ConvolutionInitialImage.pieceBilinear (s • Q i) (L i)) = _
    simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]
    rfl

/-- Vary all quadratic coefficients while fixing the tuple of degree-one classes. -/
def coefficientMap (L : SourceTuple K t w q) : Coefficients K t w q →ₗ[K] Piece K t w 3 :=
  bilinear.flip L

@[simp] theorem coefficientMap_apply (L : SourceTuple K t w q) (Q : Coefficients K t w q) :
    coefficientMap L Q = outerMap Q L := rfl

/-- The actual subspace spanned by the source tuple. -/
def tupleSpan (L : SourceTuple K t w q) : Submodule K (Piece K t w 1) :=
  Submodule.span K (Set.range L)

/-- Fixed-tuple coefficient range equals the full quadratic image of its span. -/
theorem coefficientMap_range (L : SourceTuple K t w q) :
    LinearMap.range (coefficientMap L) = quadraticImage (tupleSpan L) := by
  classical
  apply le_antisymm
  · rintro _ ⟨Q, rfl⟩
    rw [coefficientMap_apply, outerMap_apply]
    apply Submodule.sum_mem
    intro i _
    exact quadratic_multiple_mem _ _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply iSup_le
    intro f
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    refine ⟨fun i => s i • f, ?_⟩
    rw [coefficientMap_apply, outerMap_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ConvolutionInitialImage.pieceBilinear (s i • f) (L i) = pieceMul f (s i • L i)
    simp only [map_smul, LinearMap.smul_apply]
    rfl

/-- The coefficient rank is the actual image dimension, with no rank hypothesis. -/
theorem coefficientMap_finrank (L : SourceTuple K t w q) :
    finrank K (LinearMap.range (coefficientMap L)) = finrank K (quadraticImage (tupleSpan L)) := by
  rw [coefficientMap_range]

/-- The tuple's span has dimension at most the number of tuple entries. -/
theorem tupleSpan_finrank_le_length (L : SourceTuple K t w q) : finrank K (tupleSpan L) ≤ q := by
  classical
  change finrank K (Submodule.span K (Set.range L)) ≤ q
  calc
    finrank K (Submodule.span K (Set.range L)) ≤ (Set.range L).toFinset.card :=
      finrank_span_le_card (R := K) (Set.range L)
    _ = Fintype.card (Set.range L) := Set.toFinset_card _
    _ ≤ q := by simpa only [Fintype.card_fin] using Fintype.card_range_le L

/-- A nonzero tuple has positive span dimension. -/
theorem tupleSpan_finrank_pos (L : SourceTuple K t w q) (hL : L ≠ 0) :
    0 < finrank K (tupleSpan L) := by
  by_contra! h
  have hz : tupleSpan L = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h)
  apply hL
  funext i
  have hi : L i ∈ tupleSpan L := Submodule.subset_span ⟨i, rfl⟩
  rw [hz] at hi
  exact hi

/-- Avoiding all nonzero source tuples in the kernel is precisely injectivity
of the actual outer multiplication map. -/
theorem injective_iff_no_nonzero_kernel (Q : Coefficients K t w q) :
    Function.Injective (outerMap Q) ↔
      ∀ L : SourceTuple K t w q, L ≠ 0 → coefficientMap L Q ≠ 0 := by
  constructor
  · intro h L hL hz
    apply hL
    exact h (hz.trans (map_zero _).symm)
  · intro h
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro L hL
    by_contra hz
    exact h L hz hL

/-- The endpoint model has exactly the manuscript's degree-one dimension. -/
theorem source_finrank (c : ℕ) (hc : 4 ≤ c) (w : ℕ) :
    finrank K (Piece K (coreP c + 1) w 1) = coreA c + 3 * w := by
  have ht : 2 ≤ coreP c + 1 := by unfold coreP; omega
  rw [(pieceSuccEquiv (K := K) (t := coreP c + 1) (w := w) (j := 0)).finrank_eq,
    ConvolutionFree.degreeOne_finrank ht]
  simp only [Nat.add_sub_cancel, coreA]

/-- The actual source dimension at either canonical endpoint. -/
theorem endpoint_source_finrank (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    finrank K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1) = totalA m (mixedCount m upper) := by
  have hc : 4 ≤ mixedCount m upper := by
    by_cases hsmall : m ≤ 319
    · exact ConvolutionFiniteImages.canonical_mixedCount_ge_four m (by omega) hsmall upper
    · exact (UniformScalar.c_range m (by omega) upper).1
  exact source_finrank _ hc _

/-- The coefficient-rank inequality for actual source tuples at every canonical
endpoint with child dimension at least 41. It is the exact natural-number
bound used with projective tuple parameter counts. -/
theorem endpoint_coefficient_rank_bound [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (L : SourceTuple K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) (upperEndpoint m)) :
    let d := finrank K (tupleSpan L)
    d * (upperEndpoint m + totalA m (mixedCount m upper) - d) ≤
      finrank K (LinearMap.range (coefficientMap L)) := by
  have hd : finrank K (tupleSpan L) ≤ totalA m (mixedCount m upper) := by
    have h := Submodule.finrank_le (tupleSpan L)
    rw [endpoint_source_finrank m hm upper] at h
    exact h
  have h := ConvolutionScalarImages.outer_image_bound m hm upper (tupleSpan L)
  dsimp only at h ⊢
  rw [coefficientMap_finrank]
  have hcast : ((finrank K (tupleSpan L) *
      (upperEndpoint m + totalA m (mixedCount m upper) - finrank K (tupleSpan L)) : ℕ) : ℝ) ≤
      (finrank K (quadraticImage (tupleSpan L)) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : finrank K (tupleSpan L) ≤
      upperEndpoint m + totalA m (mixedCount m upper)), Nat.cast_add] using h
  exact_mod_cast hcast

/-- The actual coefficient-rank bound in precisely the projective tuple
criterion's form d(a-d)+qd, throughout the range m≥41. -/
theorem endpoint_incidence_rank_bound [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (L : SourceTuple K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) (upperEndpoint m)) :
    let d := finrank K (tupleSpan L)
    d * (totalA m (mixedCount m upper) - d) + upperEndpoint m * d ≤
      finrank K (LinearMap.range (coefficientMap L)) := by
  have hd : finrank K (tupleSpan L) ≤ totalA m (mixedCount m upper) := by
    have h := Submodule.finrank_le (tupleSpan L)
    rw [endpoint_source_finrank m hm upper] at h
    exact h
  have h := endpoint_coefficient_rank_bound m hm upper L
  dsimp only at h ⊢
  have he : upperEndpoint m + totalA m (mixedCount m upper) - finrank K (tupleSpan L) =
      upperEndpoint m + (totalA m (mixedCount m upper) - finrank K (tupleSpan L)) := by omega
  rw [he, Nat.mul_add] at h
  simpa only [Nat.mul_comm, Nat.add_comm] using h

/-- The same inequality with the ambient dimension expressed as the finrank
of the actual degree-one quotient, for direct use with vector-space incidence. -/
theorem endpoint_actual_incidence_rank_bound [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (L : SourceTuple K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) (upperEndpoint m)) :
    let d := finrank K (tupleSpan L)
    d * (finrank K (Piece K (coreP (mixedCount m upper) + 1)
      (freeW m (mixedCount m upper)) 1) - d) + upperEndpoint m * d ≤
      finrank K (LinearMap.range (coefficientMap L)) := by
  rw [endpoint_source_finrank m hm upper]
  exact endpoint_incidence_rank_bound m hm upper L

end Quartic.ConvolutionOuterIncidence
