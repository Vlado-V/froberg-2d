import Quartic.SplitBlock31Boundaries

/-!
# Projection of full boundaries onto the actual (3,1) block

The coefficient projection is a left inverse to the block embedding. It
sends every full Koszul relation into the pure–mixed boundary space. Thus
no extra full boundary kills a nonzero class of the `(3,1)` homology model.
-/

noncomputable section
namespace Quartic.SplitBlock31
open Module MvPolynomial FreeCoefficients FreeMonomialCounts
open ConvolutionFreeMultiplication ConvolutionLayers ThreeBlockModel
variable {K : Type*} [Field K] {m c q d : ℕ}

private theorem child_rename_exponent (b : Fin m →₀ ℕ) :
    b.mapDomain (Fin.natAdd 3) = mergeExponent (0 : Fin 3 →₀ ℕ) b := by
  ext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨l, hl⟩
      have h := congrArg Fin.val hl
      simp at h
      omega
  · intro i
    rw [Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective m 3)]
    simp

/-- A pure Y-form has no coefficient at a different Y-degree. -/
theorem freeCoeff_childEmbed_degree_ne (p : Forms K m d) (b : Fin m →₀ ℕ)
    (hb : b.degree ≠ d) : freeCoeff b (childEmbed p).val = 0 := by
  classical
  rw [childEmbed_val, p.val.as_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [rename_monomial, child_rename_exponent, freeCoeff_monomial, ite_eq_right]
  intro heb
  apply hb
  have h := p.property (mem_support_iff.mp he)
  change (Finsupp.weight (fun _ : Fin m => (1 : ℕ))) e = d at h
  rw [← Finsupp.degree_eq_weight_one] at h
  exact heb ▸ h

/-- Extract the pure X-quadratic coefficient of an arbitrary total quadric. -/
def coreProjection : Forms K (3 + m) 2 →ₗ[K] Forms K 3 2 :=
  ((freeCoeff (0 : Fin m →₀ ℕ)).comp (Forms K (3 + m) 2).subtype).codRestrict _
    (fun p => by
      change (freeCoeff (0 : Fin m →₀ ℕ) p.val).IsHomogeneous 2
      simpa using freeCoeff_homogeneous p.val p.property (0 : Fin m →₀ ℕ))

/-- Extract the X-linear coefficient of every Y variable from a total quadric. -/
def linearYProjection : Forms K (3 + m) 2 →ₗ[K] (Fin m → Forms K 3 1) :=
  LinearMap.pi fun l =>
    ((freeCoeff (Finsupp.single l 1)).comp (Forms K (3 + m) 2).subtype).codRestrict _
      (fun p => by
        change (freeCoeff (Finsupp.single l 1) p.val).IsHomogeneous 1
        simpa using freeCoeff_homogeneous p.val p.property (Finsupp.single l 1))

@[simp] theorem coreProjection_coreEmbed (p : Forms K 3 2) :
    coreProjection (coreEmbed (m := m) p) = p := by
  apply Subtype.ext
  change freeCoeff (0 : Fin m →₀ ℕ) (rename (Fin.castAdd m) p.val) = p.val
  rw [← liftCoeff_zero_eq_rename, freeCoeff_liftCoeff]
  simp

@[simp] theorem linearYProjection_linearYEmbed (a : Fin m → Forms K 3 1) :
    linearYProjection (linearYEmbed a) = a := by
  funext l
  apply Subtype.ext
  exact freeCoeff_linearYEmbed a l

@[simp] theorem coreProjection_linearYEmbed (a : Fin m → Forms K 3 1) :
    coreProjection (linearYEmbed a) = 0 := by
  classical
  apply Subtype.ext
  change freeCoeff (0 : Fin m →₀ ℕ) (linearYEmbed a).val = 0
  rw [linearYEmbed_val, map_sum]
  apply Finset.sum_eq_zero
  intro l _
  rw [freeCoeff_liftCoeff, ite_eq_right]
  intro h
  have hd := congrArg Finsupp.degree h
  simp at hd

@[simp] theorem linearYProjection_coreEmbed (p : Forms K 3 2) :
    linearYProjection (coreEmbed (m := m) p) = 0 := by
  classical
  funext l
  apply Subtype.ext
  change freeCoeff (Finsupp.single l 1) (rename (Fin.castAdd m) p.val) = 0
  rw [← liftCoeff_zero_eq_rename, freeCoeff_liftCoeff, ite_eq_right]
  intro h
  have hd := congrArg Finsupp.degree h
  simp at hd

@[simp] theorem coreProjection_childEmbed (p : Forms K m 2) :
    coreProjection (childEmbed p) = 0 := by
  apply Subtype.ext
  exact freeCoeff_childEmbed_degree_ne p 0 (by simp)

@[simp] theorem linearYProjection_childEmbed (p : Forms K m 2) :
    linearYProjection (childEmbed p) = 0 := by
  funext l
  apply Subtype.ext
  exact freeCoeff_childEmbed_degree_ne p (Finsupp.single l 1) (by simp)

/-- Project the full coefficient source onto its `(3,1)` component. -/
def sourceProjection : (Fin (4 + (c + q)) → Forms K (3 + m) 2) →ₗ[K]
    SplitMiddle31.Source K m c :=
  (LinearMap.pi (fun j => coreProjection.comp (LinearMap.proj (Fin.natAdd 4 (Fin.castAdd q j))))).prod
    (LinearMap.pi (fun i => linearYProjection.comp (LinearMap.proj (Fin.castAdd (c + q) i))))

@[simp] theorem sourceProjection_sourceEmbedding (a : SplitMiddle31.Source K m c) :
    sourceProjection (sourceEmbedding (q := q) a) = a := by
  apply Prod.ext
  · funext j
    change coreProjection (sourceEmbedding a (Fin.natAdd 4 (Fin.castAdd q j))) = a.1 j
    simp
  · funext i
    change linearYProjection (sourceEmbedding a (Fin.castAdd (c + q) i)) = a.2 i
    simp

/-- A pairwise commutativity relation, without imposing an order on its indices. -/
def pairVector (A : Fin (4 + (c + q)) → Forms K (3 + m) 2)
    (i j : Fin (4 + (c + q))) : Fin (4 + (c + q)) → Forms K (3 + m) 2 :=
  fun k => (if k = i then A j else 0) - (if k = j then A i else 0)

theorem pairVector_swap (A : Fin (4 + (c + q)) → Forms K (3 + m) 2)
    (i j : Fin (4 + (c + q))) : pairVector A j i = -pairVector A i j := by
  funext k
  exact (neg_sub _ _).symm

@[simp] theorem sourceProjection_pair_fst
    (A : Fin (4 + (c + q)) → Forms K (3 + m) 2) (u v : Fin (4 + (c + q))) (j : Fin c) :
    (sourceProjection (pairVector A u v)).1 j =
      (if Fin.natAdd 4 (Fin.castAdd q j) = u then coreProjection (A v) else 0) -
      (if Fin.natAdd 4 (Fin.castAdd q j) = v then coreProjection (A u) else 0) := by
  classical
  change coreProjection ((if Fin.natAdd 4 (Fin.castAdd q j) = u then A v else 0) -
    (if Fin.natAdd 4 (Fin.castAdd q j) = v then A u else 0)) = _
  split_ifs <;> simp_all only [map_sub, map_zero]

@[simp] theorem sourceProjection_pair_snd
    (A : Fin (4 + (c + q)) → Forms K (3 + m) 2) (u v : Fin (4 + (c + q))) (i : Fin 4) :
    (sourceProjection (pairVector A u v)).2 i =
      (if Fin.castAdd (c + q) i = u then linearYProjection (A v) else 0) -
      (if Fin.castAdd (c + q) i = v then linearYProjection (A u) else 0) := by
  classical
  change linearYProjection ((if Fin.castAdd (c + q) i = u then A v else 0) -
    (if Fin.castAdd (c + q) i = v then A u else 0)) = _
  split_ifs <;> simp_all only [map_sub, map_zero]

private theorem projection_cross_mem (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) (i : Fin 4) (j : Fin c) :
    sourceProjection (pairVector (generators g Q) (Fin.castAdd (c + q) i)
      (Fin.natAdd 4 (Fin.castAdd q j))) ∈ LinearMap.range (SplitMiddle31.boundary g) := by
  classical
  let t : SplitMiddle31.BoundarySource K c := Pi.single i (Pi.single j 1)
  have h : sourceEmbedding (SplitMiddle31.boundary g t) =
      -pairVector (generators g Q) (Fin.castAdd (c + q) i) (Fin.natAdd 4 (Fin.castAdd q j)) := by
    change sourceEmbedding (SplitMiddle31.boundary g t) =
      -koszulVector (generators g Q) (crossPair i j)
    simpa [t, Pi.single_apply, ite_apply, ite_smul] using
      sourceEmbedding_boundary g Q t
  have hp := congrArg (sourceProjection (K := K) (m := m) (c := c) (q := q)) h
  rw [sourceProjection_sourceEmbedding, map_neg] at hp
  refine ⟨-t, ?_⟩
  rw [map_neg, hp, neg_neg]

/-- Projection of every pairwise full relation is an incoming pure–mixed boundary. -/
theorem sourceProjection_pair_mem (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) (u v : Fin (4 + (c + q))) :
    sourceProjection (pairVector (generators g Q) u v) ∈
      LinearMap.range (SplitMiddle31.boundary g) := by
  classical
  refine Fin.addCases ?_ ?_ u
  · intro i
    refine Fin.addCases ?_ ?_ v
    · intro j
      have hz : sourceProjection (pairVector (generators g Q)
          (Fin.castAdd (c + q) i) (Fin.castAdd (c + q) j)) = 0 := by
        apply Prod.ext <;> funext k <;> simp
      rw [hz]
      exact Submodule.zero_mem _
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro k
        exact projection_cross_mem g Q i k
      · intro k
        have hz : sourceProjection (pairVector (generators g Q)
            (Fin.castAdd (c + q) i) (Fin.natAdd 4 (Fin.natAdd c k))) = 0 := by
          apply Prod.ext <;> funext l <;> simp
        rw [hz]
        exact Submodule.zero_mem _
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      refine Fin.addCases ?_ ?_ v
      · intro k
        rw [pairVector_swap, map_neg]
        exact Submodule.neg_mem _ (projection_cross_mem g Q k j)
      · intro k
        refine Fin.addCases ?_ ?_ k
        · intro l
          have hz : sourceProjection (pairVector (generators g Q)
              (Fin.natAdd 4 (Fin.castAdd q j)) (Fin.natAdd 4 (Fin.castAdd q l))) = 0 := by
            apply Prod.ext <;> funext k <;> simp
          rw [hz]
          exact Submodule.zero_mem _
        · intro l
          have hz : sourceProjection (pairVector (generators g Q)
              (Fin.natAdd 4 (Fin.castAdd q j)) (Fin.natAdd 4 (Fin.natAdd c l))) = 0 := by
            apply Prod.ext <;> funext k <;> simp
          rw [hz]
          exact Submodule.zero_mem _
    · intro j
      have hz : ∀ v : Fin (4 + (c + q)),
          sourceProjection (pairVector (generators g Q) (Fin.natAdd 4 (Fin.natAdd c j)) v) = 0 := by
        intro v
        refine Fin.addCases ?_ ?_ v
        · intro k
          apply Prod.ext <;> funext l <;> simp
        · intro k
          refine Fin.addCases ?_ ?_ k <;> intro l
          all_goals apply Prod.ext <;> funext k <;> simp
      rw [hz]
      exact Submodule.zero_mem _

/-- No full Koszul boundary has a new boundary class in bidegree (3,1). -/
theorem sourceProjection_koszul_mem (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) (a : Fin (4 + (c + q)) → Forms K (3 + m) 2)
    (ha : a ∈ koszulSpace (generators g Q)) :
    sourceProjection a ∈ LinearMap.range (SplitMiddle31.boundary g) := by
  have hle : koszulSpace (generators g Q) ≤
      (LinearMap.range (SplitMiddle31.boundary g)).comap sourceProjection := by
    apply Submodule.span_le.mpr
    rintro a ⟨p, rfl⟩
    exact sourceProjection_pair_mem g Q p.val.1 p.val.2
  exact hle ha

/-- The embedded incoming space is precisely the full boundary space pulled back to the block. -/
theorem sourceEmbedding_comap_koszul (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) :
    (koszulSpace (generators g Q)).comap sourceEmbedding =
      LinearMap.range (SplitMiddle31.boundary g) := by
  ext a
  constructor
  · intro ha
    have h := sourceProjection_koszul_mem g Q (sourceEmbedding a) ha
    simpa only [sourceProjection_sourceEmbedding] using h
  · rintro ⟨t, rfl⟩
    exact sourceEmbedding_boundary_mem g Q t

/-- The actual (3,1) homology embeds injectively in the full quartic homology. -/
theorem homologyMap_injective (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) : Function.Injective (homologyMap g Q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  revert hx
  refine Submodule.Quotient.induction_on _ x ?_
  intro a ha
  rw [homologyMap_mk] at ha
  have hb := (Submodule.Quotient.mk_eq_zero _).mp ha
  have hfull : sourceEmbedding a.val ∈ koszulSpace (generators g Q) := hb
  have hblock : a.val ∈ LinearMap.range (SplitMiddle31.boundary g) := by
    have h := sourceProjection_koszul_mem g Q (sourceEmbedding a.val) hfull
    simpa only [sourceProjection_sourceEmbedding] using h
  exact (Submodule.Quotient.mk_eq_zero _).mpr hblock

/-- The resulting actual subspace of full homology has the uniform source dimension `2m+2c`. -/
theorem homologyMap_range_finrank (g : SplitMiddle31.Mixed K m c)
    (Q : Fin q → Forms K m 2) :
    finrank K (LinearMap.range (homologyMap g Q)) = 2 * m + 2 * c := by
  rw [LinearMap.finrank_range_of_inj (homologyMap_injective g Q)]
  exact SplitMiddle31.homology_finrank g

end Quartic.SplitBlock31
