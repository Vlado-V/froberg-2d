import Quartic.SplitBlock31Projection

/-!
# The actual pure (4,0) block of the full split complex

The three-dimensional homology of the four pure quadrics embeds in the
full quartic homology, with exact reflection of incoming boundaries. Its
entire target component is already filled by the pure multiplication map.
-/

noncomputable section
namespace Quartic.SplitBlock40
open Module MvPolynomial ThreeBlockModel
open SplitBlock31
variable {K : Type*} [Field K] {m c q : ℕ}

/-- Insert pure X-quadratic coefficients and set all mixed/child coefficients to zero. -/
def sourceEmbedding : (Fin 4 → Forms K 3 2) →ₗ[K]
    (Fin (4 + (c + q)) → Forms K (3 + m) 2) where
  toFun a := Fin.addCases (fun i => coreEmbed (a i)) (fun _ => 0)
  map_add' a b := by funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  map_smul' s a := by funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

@[simp] theorem sourceEmbedding_pure (a : Fin 4 → Forms K 3 2) (i : Fin 4) :
    sourceEmbedding (m := m) (c := c) (q := q) a (Fin.castAdd (c + q) i) = coreEmbed (a i) := by
  simp [sourceEmbedding]

@[simp] theorem sourceEmbedding_other (a : Fin 4 → Forms K 3 2) (j : Fin (c + q)) :
    sourceEmbedding (m := m) (c := c) (q := q) a (Fin.natAdd 4 j) = 0 := by
  simp [sourceEmbedding]

/-- Read the pure X component of each pure-generator coefficient. -/
def sourceProjection : (Fin (4 + (c + q)) → Forms K (3 + m) 2) →ₗ[K]
    (Fin 4 → Forms K 3 2) :=
  LinearMap.pi fun i => coreProjection.comp (LinearMap.proj (Fin.castAdd (c + q) i))

@[simp] theorem sourceProjection_sourceEmbedding (a : Fin 4 → Forms K 3 2) :
    sourceProjection (sourceEmbedding (m := m) (c := c) (q := q) a) = a := by
  funext i
  change coreProjection (sourceEmbedding a (Fin.castAdd (c + q) i)) = a i
  simp

theorem sourceEmbedding_injective : Function.Injective
    (sourceEmbedding (K := K) (m := m) (c := c) (q := q)) :=
  Function.LeftInverse.injective sourceProjection_sourceEmbedding

/-- The pure multiplication block is the restriction of the full actual map. -/
theorem multiplication_commutes (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : Fin 4 → Forms K 3 2) :
    quadraticMultiplication (generators g Q) (sourceEmbedding a) =
      coreEmbed (quadraticMultiplication (blockQuadrics (K := K)) a) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val, coreEmbed_val, quadraticMultiplication_val]
  simp only [Fin.sum_univ_add, sourceEmbedding_pure, sourceEmbedding_other,
    generators_pure, coreEmbed_val, Submodule.coe_zero, mul_zero, Finset.sum_const_zero,
    add_zero, map_sum, map_mul]

/-- The whole pure quartic target component is in the full multiplication image. -/
theorem pure_target_le_range (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    LinearMap.range (coreEmbed (K := K) (m := m) (d := 4)) ≤
      LinearMap.range (quadraticMultiplication (generators g Q)) := by
  rintro p ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := blockMultiplication_surjective b
  exact ⟨sourceEmbedding a, multiplication_commutes g Q a⟩

/-- A pure pair embeds as the same pair of full generators. -/
def purePair (p : GeneratorPair 4) : GeneratorPair (4 + (c + q)) :=
  ⟨(Fin.castAdd (c + q) p.val.1, Fin.castAdd (c + q) p.val.2), p.property⟩

theorem sourceEmbedding_koszul (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (p : GeneratorPair 4) :
    sourceEmbedding (koszulVector (blockQuadrics (K := K)) p) =
      koszulVector (generators g Q) (purePair p) := by
  classical
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [sourceEmbedding_pure]
    change coreEmbed ((if i = p.val.1 then blockQuadrics p.val.2 else 0) -
      (if i = p.val.2 then blockQuadrics p.val.1 else 0)) = _
    simp only [map_sub, koszulVector, purePair, Fin.castAdd_inj, generators_pure]
    split_ifs <;> simp_all
  · intro i
    rw [sourceEmbedding_other]
    simp [koszulVector, purePair]

/-- Pure incoming boundaries remain genuine full Koszul boundaries. -/
theorem sourceEmbedding_boundary_mem (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : Fin 4 → Forms K 3 2) (ha : a ∈ koszulSpace (blockQuadrics (K := K))) :
    sourceEmbedding a ∈ koszulSpace (generators g Q) := by
  have hle : koszulSpace (blockQuadrics (K := K)) ≤
      (koszulSpace (generators g Q)).comap sourceEmbedding := by
    apply Submodule.span_le.mpr
    rintro a ⟨p, rfl⟩
    change sourceEmbedding (koszulVector (blockQuadrics (K := K)) p) ∈ koszulSpace (generators g Q)
    rw [sourceEmbedding_koszul g Q p]
    exact Submodule.subset_span ⟨purePair p, rfl⟩
  exact hle ha

private theorem unordered_pair_mem {r n : ℕ} (A : Fin r → Forms K n 2) (i j : Fin r) :
    (fun k => (if k = i then A j else 0) - (if k = j then A i else 0)) ∈ koszulSpace A := by
  classical
  rcases lt_trichotomy i j with hij | hij | hji
  · exact Submodule.subset_span ⟨⟨(i, j), hij⟩, rfl⟩
  · subst j
    have hz : (fun k => (if k = i then A i else 0) - (if k = i then A i else 0)) =
        (0 : Fin r → Forms K n 2) := by funext k; exact sub_self _
    rw [hz]
    exact (koszulSpace A).zero_mem
  · have h := (koszulSpace A).neg_mem (Submodule.subset_span ⟨⟨(j, i), hji⟩, rfl⟩)
    have he : -koszulVector A ⟨(j, i), hji⟩ =
        (fun k => (if k = i then A j else 0) - (if k = j then A i else 0)) := by
      funext k
      exact neg_sub _ _
    rwa [he] at h

@[simp] theorem sourceProjection_pair_apply
    (A : Fin (4 + (c + q)) → Forms K (3 + m) 2) (u v : Fin (4 + (c + q))) (i : Fin 4) :
    sourceProjection (pairVector A u v) i =
      (if Fin.castAdd (c + q) i = u then coreProjection (A v) else 0) -
      (if Fin.castAdd (c + q) i = v then coreProjection (A u) else 0) := by
  classical
  change coreProjection ((if Fin.castAdd (c + q) i = u then A v else 0) -
    (if Fin.castAdd (c + q) i = v then A u else 0)) = _
  split_ifs <;> simp_all only [map_sub, map_zero]

/-- Only pure–pure full boundaries have a nonzero pure-block projection. -/
theorem sourceProjection_pair_mem (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (u v : Fin (4 + (c + q))) :
    sourceProjection (pairVector (generators g Q) u v) ∈ koszulSpace (blockQuadrics (K := K)) := by
  classical
  refine Fin.addCases ?_ ?_ u
  · intro i
    refine Fin.addCases ?_ ?_ v
    · intro j
      have he : sourceProjection (pairVector (generators g Q)
          (Fin.castAdd (c + q) i) (Fin.castAdd (c + q) j)) =
          fun k => (if k = i then blockQuadrics j else 0) -
            (if k = j then blockQuadrics i else 0) := by
        funext k
        simp
      rw [he]
      exact unordered_pair_mem _ i j
    · intro j
      have hz : sourceProjection (pairVector (generators g Q)
          (Fin.castAdd (c + q) i) (Fin.natAdd 4 j)) = 0 := by
        refine Fin.addCases ?_ ?_ j <;> intro k <;> funext l <;> simp
      rw [hz]
      exact Submodule.zero_mem _
  · intro i
    have hz : sourceProjection (pairVector (generators g Q) (Fin.natAdd 4 i) v) = 0 := by
      refine Fin.addCases ?_ ?_ i <;> intro j <;> funext k <;> simp
    rw [hz]
    exact Submodule.zero_mem _

/-- Projecting a full boundary gives a boundary of the pure block. -/
theorem sourceProjection_koszul_mem (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : Fin (4 + (c + q)) → Forms K (3 + m) 2) (ha : a ∈ koszulSpace (generators g Q)) :
    sourceProjection a ∈ koszulSpace (blockQuadrics (K := K)) := by
  have hle : koszulSpace (generators g Q) ≤
      (koszulSpace (blockQuadrics (K := K))).comap sourceProjection := by
    apply Submodule.span_le.mpr
    rintro a ⟨p, rfl⟩
    exact sourceProjection_pair_mem g Q p.val.1 p.val.2
  exact hle ha

/-- Exact incoming-boundary reflection for the pure source component. -/
theorem sourceEmbedding_comap_koszul (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    (koszulSpace (generators g Q)).comap sourceEmbedding = koszulSpace (blockQuadrics (K := K)) := by
  ext a
  constructor
  · intro ha
    have h := sourceProjection_koszul_mem g Q (sourceEmbedding a) ha
    simpa only [sourceProjection_sourceEmbedding] using h
  · exact sourceEmbedding_boundary_mem g Q a

/-- Pure cycles embedded in the full actual quartic kernel. -/
def cycleEmbedding (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    (quadraticMultiplication (blockQuadrics (K := K))).ker →ₗ[K]
      (quadraticMultiplication (generators g Q)).ker :=
  (sourceEmbedding.comp (quadraticMultiplication (blockQuadrics (K := K))).ker.subtype).codRestrict _
    (fun a => by
      change quadraticMultiplication (generators g Q) (sourceEmbedding a.val) = 0
      rw [multiplication_commutes, show quadraticMultiplication blockQuadrics a.val = 0 from a.property,
        map_zero])

private def mapCycleQuotients {V W V' W' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (f : V →ₗ[K] W) (f' : V' →ₗ[K] W') (B : Submodule K V) (B' : Submodule K V')
    (e : f.ker →ₗ[K] f'.ker)
    (he : kernelBoundary f B ≤ (kernelBoundary f' B').comap e) :
    KernelModulo f B →ₗ[K] KernelModulo f' B' :=
  (kernelBoundary f B).mapQ (kernelBoundary f' B') e he

/-- Canonical map from the pure quartic homology into the actual full homology. -/
def homologyMap (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    QuarticHomology (blockQuadrics (K := K)) →ₗ[K] QuarticHomology (generators g Q) :=
  mapCycleQuotients (quadraticMultiplication (blockQuadrics (K := K)))
    (quadraticMultiplication (generators g Q)) (koszulSpace (blockQuadrics (K := K)))
    (koszulSpace (generators g Q)) (cycleEmbedding g Q) (by
      intro a ha
      exact sourceEmbedding_boundary_mem g Q a.val ha)

@[simp] theorem homologyMap_mk (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : (quadraticMultiplication (blockQuadrics (K := K))).ker) :
    homologyMap g Q (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (cycleEmbedding g Q a) := rfl

/-- No additional full boundary collapses the pure homology. -/
theorem homologyMap_injective (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    Function.Injective (homologyMap g Q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  revert hx
  refine Submodule.Quotient.induction_on _ x ?_
  intro a ha
  rw [homologyMap_mk] at ha
  have hb := (Submodule.Quotient.mk_eq_zero _).mp ha
  have hfull : sourceEmbedding a.val ∈ koszulSpace (generators g Q) := hb
  have hblock : a.val ∈ koszulSpace (blockQuadrics (K := K)) := by
    have h := sourceProjection_koszul_mem g Q (sourceEmbedding a.val) hfull
    simpa only [sourceProjection_sourceEmbedding] using h
  exact (Submodule.Quotient.mk_eq_zero _).mpr hblock

/-- The pure bidegree contributes an actual three-dimensional subspace of full homology. -/
theorem homologyMap_range_finrank (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    finrank K (LinearMap.range (homologyMap g Q)) = 3 := by
  rw [LinearMap.finrank_range_of_inj (homologyMap_injective g Q)]
  exact blockHomology_finrank

end Quartic.SplitBlock40
