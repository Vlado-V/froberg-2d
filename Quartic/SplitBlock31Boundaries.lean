import Quartic.SplitBlock31

/-!
# Actual Koszul cross-boundaries in bidegree (3,1)

The incoming boundary map of the `(3,1)` coefficient model embeds into the
span of the actual full Koszul relations of the split generators.
-/

noncomputable section
namespace Quartic.SplitBlock31
open Module MvPolynomial ThreeBlockModel
variable {K : Type*} [Field K] {m c q : ℕ}

@[simp] theorem generators_pure (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (i : Fin 4) : generators g Q (Fin.castAdd (c + q) i) = coreEmbed (blockQuadrics i) := by
  simp [generators]

@[simp] theorem generators_mixed (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (j : Fin c) : generators g Q (Fin.natAdd 4 (Fin.castAdd q j)) = linearYEmbed (g j) := by
  simp [generators]

@[simp] theorem generators_child (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (k : Fin q) : generators g Q (Fin.natAdd 4 (Fin.natAdd c k)) = childEmbed (Q k) := by
  simp [generators]

/-- The full-generator pair belonging to a pure and mixed generator. -/
def crossPair (i : Fin 4) (j : Fin c) : GeneratorPair (4 + (c + q)) :=
  ⟨(Fin.castAdd (c + q) i, Fin.natAdd 4 (Fin.castAdd q j)), by
    change i.val < 4 + j.val
    omega⟩

@[simp] private theorem leftIndex_ne_rightIndex {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = a + j.val at hv
  omega

@[simp] private theorem rightIndex_ne_leftIndex {a b : ℕ} (i : Fin a) (j : Fin b) :
    Fin.natAdd a j ≠ Fin.castAdd b i := (leftIndex_ne_rightIndex i j).symm

/-- Every incoming (3,1) boundary is the indicated sum of full Koszul boundaries. -/
theorem sourceEmbedding_boundary (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (t : SplitMiddle31.BoundarySource K c) :
    sourceEmbedding (SplitMiddle31.boundary g t) =
      -(∑ i : Fin 4, ∑ j : Fin c, t i j • koszulVector (generators g Q) (crossPair i j)) := by
  classical
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [sourceEmbedding_pure, SplitMiddle31.boundary_snd_vector]
    simp [koszulVector, crossPair, Finset.sum_apply, map_sum, map_smul, smul_ite]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro j
      rw [sourceEmbedding_mixed, SplitMiddle31.boundary_fst]
      simp [koszulVector, crossPair, Finset.sum_apply, map_sum, map_smul, smul_ite]
    · intro l
      rw [sourceEmbedding_child]
      simp [koszulVector, crossPair, Finset.sum_apply]

/-- The model's boundary image lies in the genuine full incoming Koszul space. -/
theorem sourceEmbedding_boundary_mem (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) (t : SplitMiddle31.BoundarySource K c) :
    sourceEmbedding (SplitMiddle31.boundary g t) ∈ koszulSpace (generators g Q) := by
  rw [sourceEmbedding_boundary g Q t]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨crossPair i j, rfl⟩

/-- Every embedded block cycle is an actual full quartic cycle. -/
def cycleEmbedding (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    (SplitMiddle31.multiplication g).ker →ₗ[K]
      (quadraticMultiplication (generators g Q)).ker :=
  (sourceEmbedding.comp (SplitMiddle31.multiplication g).ker.subtype).codRestrict _
    (fun a => (sourceEmbedding_kernel g Q a.val).mpr a.property)

theorem cycleEmbedding_injective (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    Function.Injective (cycleEmbedding g Q) := by
  intro a b h
  apply Subtype.ext
  apply sourceEmbedding_injective (q := q)
  exact congrArg Subtype.val h

private def quotientOfCycleMap {V W V' W' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (f : V →ₗ[K] W) (f' : V' →ₗ[K] W') (B : Submodule K V) (B' : Submodule K V')
    (e : f.ker →ₗ[K] f'.ker)
    (he : kernelBoundary f B ≤ (kernelBoundary f' B').comap e) :
    KernelModulo f B →ₗ[K] KernelModulo f' B' :=
  (kernelBoundary f B).mapQ (kernelBoundary f' B') e he

/-- The coefficient-model homology has a canonical map into full actual Koszul homology. -/
def homologyMap (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    SplitMiddle31.Homology g →ₗ[K] QuarticHomology (generators g Q) :=
  quotientOfCycleMap (SplitMiddle31.multiplication g) (quadraticMultiplication (generators g Q))
    (LinearMap.range (SplitMiddle31.boundary g)) (koszulSpace (generators g Q))
    (cycleEmbedding g Q) (by
      intro a ha
      obtain ⟨t, ht⟩ := ha
      change sourceEmbedding a.val ∈ koszulSpace (generators g Q)
      change SplitMiddle31.boundary g t = a.val at ht
      rw [← ht]
      exact sourceEmbedding_boundary_mem g Q t)

@[simp] theorem homologyMap_mk (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : (SplitMiddle31.multiplication g).ker) :
    homologyMap g Q (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (cycleEmbedding g Q a) := rfl

end Quartic.SplitBlock31
