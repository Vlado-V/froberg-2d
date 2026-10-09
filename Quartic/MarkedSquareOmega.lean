module

public import Quartic.MarkedSquareEmbedding
public import Quartic.AugmentedMiddleOmega

@[expose] public section

/-!
# The augmented witness retaining a marked square

One additional child quadratic coordinate preserves the square of an actual
mixed marked generator. Three quotient motions then separate pure homology
for any distinguished direction `ωu-v` with `ω ≠ 0,-1`.
-/

noncomputable section
namespace Quartic.MarkedSquareOmega
open Module AugmentedMiddle MarkedSquareEmbedding

variable {K : Type*} [Field K] {m c q : ℕ}

/-- The concrete D12 witness, including the independent marked-square
coordinate and simultaneous restriction to every distinguished subspace. -/
theorem marked_augmented_witness (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hc : c < m) (hbudget : q + (c + 1).choose 2 + 4 ≤ (m + 1).choose 2) :
    LinearIndependent K (AugmentedMiddle.mixedFamily (K := K) hc.le) ∧
    MiddleCoordinates.projectedProduct (zeta (K := K) hc) (zeta hc) =
      (extraSquare hc, 0) ∧
    ∃ Q : Submodule K (Forms K m 2), finrank K Q = q ∧
      Function.Injective (quotientAlong (embedding hc) Q) ∧
      ∃ r : Fin 4 → Forms K m 2 ⧸ Q, r 3 = 0 ∧
        Function.Injective
          (AugmentedMiddleOmega.augmentedMap ω (quotientAlong (embedding hc) Q) r) ∧
        ∀ U : Submodule K (Forms K m 2 ⧸ Q),
          Function.Injective (AugmentedMiddleOmega.augmentedOnSubspace ω
            (quotientAlong (embedding hc) Q) r U) := by
  refine ⟨mixedFamily_independent hc.le, zeta_product hc, ?_⟩
  obtain ⟨Q, hQ, hfQ, r, hr, hinj⟩ := AugmentedMiddleOmega.exists_quotient_motions
    ω hω hω1 (embedding (K := K) hc) (embedding_injective hc) q
    (by rw [finrank_source, finrank_quadrics]; omega)
  exact ⟨Q, hQ, hfQ, r, hr, hinj,
    AugmentedMiddleOmega.augmentedOnSubspace_injective ω _ r hinj⟩

end Quartic.MarkedSquareOmega
