import Quartic.SplitBlock22Full

/-!
# Exact boundary reflection for the full (2,2) block

The two incoming relation types are actual full Koszul vectors. Conversely,
projection of every full Koszul vector belongs to their span. Thus the
constructed homology embeds in the full quartic homology without any extra
boundary identifications.
-/
noncomputable section
namespace Quartic.SplitBlock22
open Module MvPolynomial ThreeBlockModel
open SplitBlock31 (pairVector pairVector_swap)
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q : ℕ}

/-- The full pure–child generator pair. -/
def fullCrossPair (i : Fin 4) (j : Fin q) : GeneratorPair (4+(c+q)) :=
  ⟨(Fin.castAdd (c+q) i, Fin.natAdd 4 (Fin.natAdd c j)), by
    change i.val < 4 + (c+j.val)
    omega⟩

/-- A pair of mixed indices, with its order preserved in the full family. -/
def fullMixedPair (p : GeneratorPair c) : GeneratorPair (4+(c+q)) :=
  ⟨(Fin.natAdd 4 (Fin.castAdd q p.val.1), Fin.natAdd 4 (Fin.castAdd q p.val.2)), by
    change 4+p.val.1.val < 4+p.val.2.val
    exact Nat.add_lt_add_left p.property 4⟩

/-- Each explicit pure–child array is the indicated sum of actual full Koszul vectors. -/
theorem sourceEmbedding_crossBoundary (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (b : CrossCoefficients K q) :
    sourceEmbedding (crossBoundary (c := c) h b) =
      ∑ i : Fin 4, ∑ j : Fin q, b (i,j) • koszulVector (fullGenerators g h) (fullCrossPair i j) := by
  classical
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [sourceEmbedding_pure]
    simp [crossBoundary, koszulVector, fullCrossPair, Finset.sum_apply, map_sum, map_smul, smul_ite]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro j
      rw [sourceEmbedding_mixed]
      simp [crossBoundary, koszulVector, fullCrossPair, Finset.sum_apply]
    · intro j
      rw [sourceEmbedding_child]
      simp [crossBoundary, koszulVector, fullCrossPair, Finset.sum_apply, map_sum, map_smul, smul_ite]

/-- Each mixed–mixed array is its actual full Koszul vector. -/
theorem sourceEmbedding_mixedBoundary (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : GeneratorPair c) :
    sourceEmbedding (mixedSourceEmbedding (q := q) (koszulVector g p)) =
      koszulVector (fullGenerators g h) (fullMixedPair p) := by
  classical
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [mixedSourceEmbedding, koszulVector, fullMixedPair]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro j
      rw [sourceEmbedding_mixed]
      change mixedEmbedding ((if j = p.val.1 then g p.val.2 else 0) -
        (if j = p.val.2 then g p.val.1 else 0)) = _
      simp only [map_sub, koszulVector, fullMixedPair, Fin.natAdd_inj, Fin.castAdd_inj,
        fullGenerators_mixed]
      split_ifs <;> simp_all
    · intro j
      simp [mixedSourceEmbedding, koszulVector, fullMixedPair]

/-- Every incoming block boundary maps to a genuine full Koszul boundary. -/
theorem sourceEmbedding_boundary_mem (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Source K m c q) (ha : a ∈ blockBoundarySpace g h) :
    sourceEmbedding a ∈ koszulSpace (fullGenerators g h) := by
  have hcross : crossSpace h ≤ (koszulSpace (fullGenerators g h)).comap sourceEmbedding := by
    rintro _ ⟨b,rfl⟩
    change sourceEmbedding (crossBoundary h b) ∈ koszulSpace (fullGenerators g h)
    rw [sourceEmbedding_crossBoundary g h b]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨fullCrossPair i j,rfl⟩
  have hmixed : mixedKoszulSpace g ≤ (koszulSpace (fullGenerators g h)).comap
      (sourceEmbedding.comp mixedSourceEmbedding) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change sourceEmbedding (mixedSourceEmbedding (koszulVector g p)) ∈ koszulSpace (fullGenerators g h)
    rw [sourceEmbedding_mixedBoundary]
    exact Submodule.subset_span ⟨fullMixedPair p,rfl⟩
  have hle : blockBoundarySpace g h ≤ (koszulSpace (fullGenerators g h)).comap sourceEmbedding := by
    apply sup_le hcross
    rintro _ ⟨b,hb,rfl⟩
    exact hmixed hb
  exact hle ha

@[simp] theorem sourceProjection_pair_pure
    (A : Fin (4+(c+q)) → Forms K (3+m) 2) (u v : Fin (4+(c+q))) (i : Fin 4) :
    (sourceProjection (pairVector A u v)).1 i =
      (if Fin.castAdd (c+q) i = u then childProjection (A v) else 0) -
      (if Fin.castAdd (c+q) i = v then childProjection (A u) else 0) := by
  classical
  change childProjection ((if Fin.castAdd (c+q) i = u then A v else 0) -
    (if Fin.castAdd (c+q) i = v then A u else 0)) = _
  split_ifs <;> simp_all only [map_sub, map_zero]

@[simp] theorem sourceProjection_pair_mixed
    (A : Fin (4+(c+q)) → Forms K (3+m) 2) (u v : Fin (4+(c+q))) (i : Fin c) :
    (sourceProjection (pairVector A u v)).2.1 i =
      (if Fin.natAdd 4 (Fin.castAdd q i) = u then middleProjection (A v) else 0) -
      (if Fin.natAdd 4 (Fin.castAdd q i) = v then middleProjection (A u) else 0) := by
  classical
  change middleProjection ((if Fin.natAdd 4 (Fin.castAdd q i) = u then A v else 0) -
    (if Fin.natAdd 4 (Fin.castAdd q i) = v then A u else 0)) = _
  split_ifs <;> simp_all only [map_sub, map_zero]

@[simp] theorem sourceProjection_pair_child
    (A : Fin (4+(c+q)) → Forms K (3+m) 2) (u v : Fin (4+(c+q))) (i : Fin q) :
    (sourceProjection (pairVector A u v)).2.2 i =
      (if Fin.natAdd 4 (Fin.natAdd c i) = u then SplitBlock31.coreProjection (A v) else 0) -
      (if Fin.natAdd 4 (Fin.natAdd c i) = v then SplitBlock31.coreProjection (A u) else 0) := by
  classical
  change SplitBlock31.coreProjection ((if Fin.natAdd 4 (Fin.natAdd c i) = u then A v else 0) -
    (if Fin.natAdd 4 (Fin.natAdd c i) = v then A u else 0)) = _
  split_ifs <;> simp_all only [map_sub, map_zero]

private theorem projection_cross_mem (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (i : Fin 4) (j : Fin q) :
    sourceProjection (pairVector (fullGenerators g h) (Fin.castAdd (c+q) i)
      (Fin.natAdd 4 (Fin.natAdd c j))) ∈ blockBoundarySpace g h := by
  classical
  let b : CrossCoefficients K q := Pi.single (i,j) 1
  have he : sourceEmbedding (crossBoundary (c := c) h b) =
      pairVector (fullGenerators g h) (Fin.castAdd (c+q) i) (Fin.natAdd 4 (Fin.natAdd c j)) := by
    change sourceEmbedding (crossBoundary (c := c) h b) =
      koszulVector (fullGenerators g h) (fullCrossPair i j)
    simpa [b, Pi.single_apply, Prod.mk.injEq, ite_smul, ite_and] using sourceEmbedding_crossBoundary g h b
  have hp := congrArg (sourceProjection (K := K) (m := m) (c := c) (q := q)) he
  rw [sourceProjection_sourceEmbedding] at hp
  rw [← hp]
  exact Submodule.mem_sup_left ⟨b,rfl⟩

private theorem projection_mixed_mem (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (i j : Fin c) :
    sourceProjection (pairVector (fullGenerators g h) (Fin.natAdd 4 (Fin.castAdd q i))
      (Fin.natAdd 4 (Fin.castAdd q j))) ∈ blockBoundarySpace g h := by
  have hlt (i j : Fin c) (hij : i < j) :
      sourceProjection (pairVector (fullGenerators g h) (Fin.natAdd 4 (Fin.castAdd q i))
        (Fin.natAdd 4 (Fin.castAdd q j))) ∈ blockBoundarySpace g h := by
    let p : GeneratorPair c := ⟨(i,j),hij⟩
    have hp := congrArg (sourceProjection (K := K) (m := m) (c := c) (q := q))
      (sourceEmbedding_mixedBoundary g h p)
    rw [sourceProjection_sourceEmbedding] at hp
    change mixedSourceEmbedding (koszulVector g p) = sourceProjection
      (pairVector (fullGenerators g h) (Fin.natAdd 4 (Fin.castAdd q i))
        (Fin.natAdd 4 (Fin.castAdd q j))) at hp
    rw [← hp]
    exact Submodule.mem_sup_right ⟨koszulVector g p, Submodule.subset_span ⟨p,rfl⟩,rfl⟩
  rcases lt_trichotomy i j with hij | hij | hji
  · exact hlt i j hij
  · subst j
    have hz : pairVector (fullGenerators g h) (Fin.natAdd 4 (Fin.castAdd q i))
        (Fin.natAdd 4 (Fin.castAdd q i)) = 0 := by funext k; exact sub_self _
    rw [hz, map_zero]
    exact Submodule.zero_mem _
  · rw [pairVector_swap, map_neg]
    exact Submodule.neg_mem _ (hlt j i hji)

/-- Every full incoming Koszul vector projects to one of the two actual block boundary types. -/
theorem sourceProjection_pair_mem (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (u v : Fin (4+(c+q))) :
    sourceProjection (pairVector (fullGenerators g h) u v) ∈ blockBoundarySpace g h := by
  classical
  refine Fin.addCases ?_ ?_ u
  · intro i
    refine Fin.addCases ?_ ?_ v
    · intro j
      have hz : sourceProjection (pairVector (fullGenerators g h)
          (Fin.castAdd (c+q) i) (Fin.castAdd (c+q) j)) = 0 := by
        refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;> simp
      rw [hz]; exact Submodule.zero_mem _
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro k
        have hz : sourceProjection (pairVector (fullGenerators g h)
            (Fin.castAdd (c+q) i) (Fin.natAdd 4 (Fin.castAdd q k))) = 0 := by
          refine Prod.ext (funext fun l => ?_) (Prod.ext (funext fun l => ?_) (funext fun l => ?_)) <;> simp
        rw [hz]; exact Submodule.zero_mem _
      · intro k
        exact projection_cross_mem g h i k
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      refine Fin.addCases ?_ ?_ v
      · intro k
        have hz : sourceProjection (pairVector (fullGenerators g h)
            (Fin.natAdd 4 (Fin.castAdd q j)) (Fin.castAdd (c+q) k)) = 0 := by
          refine Prod.ext (funext fun l => ?_) (Prod.ext (funext fun l => ?_) (funext fun l => ?_)) <;> simp
        rw [hz]; exact Submodule.zero_mem _
      · intro k
        refine Fin.addCases ?_ ?_ k
        · intro l
          exact projection_mixed_mem g h j l
        · intro l
          have hz : sourceProjection (pairVector (fullGenerators g h)
              (Fin.natAdd 4 (Fin.castAdd q j)) (Fin.natAdd 4 (Fin.natAdd c l))) = 0 := by
            refine Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) <;> simp
          rw [hz]; exact Submodule.zero_mem _
    · intro j
      refine Fin.addCases ?_ ?_ v
      · intro i
        rw [pairVector_swap, map_neg]
        exact Submodule.neg_mem _ (projection_cross_mem g h i j)
      · intro k
        have hz : sourceProjection (pairVector (fullGenerators g h)
            (Fin.natAdd 4 (Fin.natAdd c j)) (Fin.natAdd 4 k)) = 0 := by
          refine Fin.addCases ?_ ?_ k <;> intro l
          all_goals
            refine Prod.ext (funext fun s => ?_) (Prod.ext (funext fun s => ?_) (funext fun s => ?_)) <;> simp
        rw [hz]; exact Submodule.zero_mem _

/-- Projection of an arbitrary full incoming boundary remains a block boundary. -/
theorem sourceProjection_koszul_mem (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Fin (4+(c+q)) → Forms K (3+m) 2)
    (ha : a ∈ koszulSpace (fullGenerators g h)) : sourceProjection a ∈ blockBoundarySpace g h := by
  have hle : koszulSpace (fullGenerators g h) ≤ (blockBoundarySpace g h).comap sourceProjection := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact sourceProjection_pair_mem g h p.val.1 p.val.2
  exact hle ha

/-- The full boundary space pulls back to exactly the already identified actual block boundaries. -/
theorem sourceEmbedding_comap_koszul (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) :
    (koszulSpace (fullGenerators g h)).comap sourceEmbedding = blockBoundarySpace g h := by
  ext a
  constructor
  · intro ha
    have hp := sourceProjection_koszul_mem g h (sourceEmbedding a) ha
    simpa only [sourceProjection_sourceEmbedding] using hp
  · exact sourceEmbedding_boundary_mem g h a

/-- Embed actual (2,2) cycles into the full quartic multiplication kernel. -/
def fullCycleEmbedding (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    (multiplication g h).ker →ₗ[K] (quadraticMultiplication (fullGenerators g h)).ker :=
  (sourceEmbedding.comp (multiplication g h).ker.subtype).codRestrict _
    (fun a => (sourceEmbedding_kernel g h a.val).mpr a.property)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical actual homology map from the block to the full indexed split complex. -/
def fullHomologyMap (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    BlockHomology g h →ₗ[K] QuarticHomology (fullGenerators g h) where
  toFun x := Quotient.liftOn x (fun a => Submodule.Quotient.mk (fullCycleEmbedding g h a)) (by
    intro a b hab
    apply (Submodule.Quotient.eq' _).mpr
    change -sourceEmbedding a.val + sourceEmbedding b.val ∈ koszulSpace (fullGenerators g h)
    simp only [HasEquiv.Equiv, instHasEquivOfSetoid, QuotientAddGroup.leftRel_apply] at hab
    change -a.val + b.val ∈ blockBoundarySpace g h at hab
    have hp := sourceEmbedding_boundary_mem g h (-a.val+b.val) hab
    simpa only [map_add, map_neg] using hp)
  map_add' x y := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro a
    refine Submodule.Quotient.induction_on _ y ?_
    intro b
    change Submodule.Quotient.mk (fullCycleEmbedding g h (a+b)) =
      Submodule.Quotient.mk (fullCycleEmbedding g h a) +
      Submodule.Quotient.mk (fullCycleEmbedding g h b)
    rw [map_add]
    rfl
  map_smul' s x := by
    refine Submodule.Quotient.induction_on _ x ?_
    intro a
    change Submodule.Quotient.mk (fullCycleEmbedding g h (s • a)) =
      s • Submodule.Quotient.mk (fullCycleEmbedding g h a)
    rw [map_smul]
    rfl

@[simp] theorem fullHomologyMap_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : (multiplication g h).ker) :
    fullHomologyMap g h (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (fullCycleEmbedding g h a) := rfl

/-- No extra boundary in the full indexed complex collapses a nonzero block homology class. -/
theorem fullHomologyMap_injective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) : Function.Injective (fullHomologyMap g h) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  revert hx
  refine Submodule.Quotient.induction_on _ x ?_
  intro a ha
  rw [fullHomologyMap_mk] at ha
  have hb := (Submodule.Quotient.mk_eq_zero _).mp ha
  have hfull : sourceEmbedding a.val ∈ koszulSpace (fullGenerators g h) := hb
  have hblock : a.val ∈ blockBoundarySpace g h := by
    have hp := sourceProjection_koszul_mem g h (sourceEmbedding a.val) hfull
    simpa only [sourceProjection_sourceEmbedding] using hp
  exact (Submodule.Quotient.mk_eq_zero _).mpr hblock

/-- The actual subspace of full homology has the manuscript's middle dimension. -/
theorem fullHomologyMap_range_finrank_eq_H (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    (finrank K (LinearMap.range (fullHomologyMap g h)) : ℤ) = Counts.H m q c := by
  rw [LinearMap.finrank_range_of_inj (fullHomologyMap_injective g h)]
  exact homology_finrank_eq_H g h hg hh hs

/-- Under the actual middle surjectivity condition, the whole (2,2) target lies in the full image. -/
theorem full_target_le_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    SplitBigrading.bidegreeSpace K 3 m 2 2 ≤
      LinearMap.range (quadraticMultiplication (fullGenerators g h)) := by
  rw [← targetEmbedding_range]
  rintro z ⟨b,rfl⟩
  obtain ⟨a,rfl⟩ := multiplication_surjective g h hs b
  exact ⟨sourceEmbedding a,full_multiplication_commutes g h a⟩

end Quartic.SplitBlock22
