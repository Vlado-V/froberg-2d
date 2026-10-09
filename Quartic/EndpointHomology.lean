module

public import Quartic.Homology
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Restricting first Koszul homology to a prefix of independent generators

The elementary boundary-intersection argument uses a correction to coordinate
restriction. It kills the Koszul boundaries involving the last generator and
acts as ordinary restriction on vectors whose last coordinate is zero.
-/

namespace Quartic.EndpointHomology

noncomputable section

section Boundaries

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}

def prefixFamily (q : Fin (r + 1) → V) : Fin r → V := fun i => q i.castSucc

def boundarySpan (q : Fin r → V) : Submodule K (Fin r → V) :=
  Submodule.span K (Set.range (Quartic.koszulVector q))

/-- Append a zero coefficient to a relation on the old generators. -/
def extendZero : (Fin r → V) →ₗ[K] (Fin (r + 1) → V) :=
  LinearMap.pi (Fin.snoc (fun i : Fin r => LinearMap.proj i) 0)

@[simp] theorem extendZero_castSucc (a : Fin r → V) (i : Fin r) :
    extendZero (K := K) a i.castSucc = a i := by
  simp [extendZero]

@[simp] theorem extendZero_last (a : Fin r → V) :
    extendZero (K := K) a (Fin.last r) = 0 := by
  simp [extendZero]

theorem extendZero_injective : Function.Injective (extendZero (K := K) (V := V) (r := r)) := by
  intro a b h
  funext i
  have hi := congrFun h i.castSucc
  simpa using hi

@[simp] theorem prefixFamily_extendZero (a : Fin r → V) :
    prefixFamily (extendZero (K := K) a) = a := by
  funext i
  exact extendZero_castSucc a i

theorem extendZero_prefixFamily (a : Fin (r + 1) → V)
    (ha : a (Fin.last r) = 0) : extendZero (K := K) (prefixFamily a) = a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [ha]
  · simp [prefixFamily]

@[simp] theorem last_ne_castSucc (i : Fin r) : Fin.last r ≠ i.castSucc :=
  (ne_of_lt (Fin.castSucc_lt_last i)).symm

def castPair (p : Quartic.GeneratorPair r) : Quartic.GeneratorPair (r + 1) :=
  ⟨(p.val.1.castSucc, p.val.2.castSucc), p.property⟩

theorem extendZero_koszulVector (q : Fin (r + 1) → V) (p : Quartic.GeneratorPair r) :
    extendZero (K := K) (Quartic.koszulVector (prefixFamily q) p) =
      Quartic.koszulVector q (castPair p) := by
  classical
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Quartic.koszulVector, castPair]
  · simp [Quartic.koszulVector, castPair, prefixFamily]

theorem extendZero_mem_boundarySpan (q : Fin (r + 1) → V)
    {a : Fin r → V} (ha : a ∈ boundarySpan (K := K) (prefixFamily q)) :
    extendZero (K := K) a ∈ boundarySpan (K := K) q := by
  have hle : boundarySpan (K := K) (prefixFamily q) ≤
      (boundarySpan (K := K) q).comap extendZero := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change extendZero (K := K) (Quartic.koszulVector (prefixFamily q) p) ∈
      boundarySpan (K := K) q
    rw [extendZero_koszulVector]
    exact Submodule.subset_span ⟨castPair p, rfl⟩
  exact hle ha

/-- A linear correction to restriction that sends every new pair boundary
to zero. The dual functionals recover the old-generator coordinates. -/
def boundaryRetraction (q : Fin (r + 1) → V)
    (dual : Fin (r + 1) → V →ₗ[K] K) :
    (Fin (r + 1) → V) →ₗ[K] (Fin r → V) where
  toFun a i := a i.castSucc + dual i.castSucc (a (Fin.last r)) • q (Fin.last r)
  map_add' a b := by
    funext i
    simp only [Pi.add_apply, map_add, add_smul]
    abel
  map_smul' c a := by
    funext i
    simp only [Pi.smul_apply, map_smul, smul_add, smul_smul,
      RingHom.id_apply, smul_eq_mul]

theorem boundaryRetraction_of_last_zero (q : Fin (r + 1) → V)
    (dual : Fin (r + 1) → V →ₗ[K] K) (a : Fin (r + 1) → V)
    (ha : a (Fin.last r) = 0) :
    boundaryRetraction q dual a = prefixFamily a := by
  funext i
  simp [boundaryRetraction, prefixFamily, ha]

theorem boundaryRetraction_generator (q : Fin (r + 1) → V)
    (dual : Fin (r + 1) → V →ₗ[K] K)
    (hdual : ∀ i j, dual i (q j) = if i = j then 1 else 0)
    (p : Quartic.GeneratorPair (r + 1)) :
    boundaryRetraction q dual (Quartic.koszulVector q p) ∈
      boundarySpan (K := K) (prefixFamily q) := by
  classical
  by_cases hj : p.val.2 = Fin.last r
  · have hi : p.val.1 ≠ Fin.last r := ne_of_lt (hj ▸ p.property)
    have hz : boundaryRetraction q dual (Quartic.koszulVector q p) = 0 := by
      funext k
      by_cases hk : k.castSucc = p.val.1
      · simp [boundaryRetraction, Quartic.koszulVector, hj, hi, Ne.symm hi, hk, hdual]
      · simp [boundaryRetraction, Quartic.koszulVector, hj, Ne.symm hi, hk, hdual]
    rw [hz]
    exact Submodule.zero_mem _
  · have hjlt : p.val.2.val < r := Fin.lt_last_iff_ne_last.mpr hj
    have hilt : p.val.1.val < r := lt_trans p.property hjlt
    let i : Fin r := ⟨p.val.1.val, hilt⟩
    let j : Fin r := ⟨p.val.2.val, hjlt⟩
    have hi : i.castSucc = p.val.1 := Fin.ext rfl
    have hj' : j.castSucc = p.val.2 := Fin.ext rfl
    let old : Quartic.GeneratorPair r := ⟨(i, j), p.property⟩
    have hvec : boundaryRetraction q dual (Quartic.koszulVector q p) =
        Quartic.koszulVector (prefixFamily q) old := by
      funext k
      simp [boundaryRetraction, Quartic.koszulVector, prefixFamily, old, ← hi, ← hj']
    rw [hvec]
    exact Submodule.subset_span ⟨old, rfl⟩

theorem boundaryRetraction_mem (q : Fin (r + 1) → V)
    (dual : Fin (r + 1) → V →ₗ[K] K)
    (hdual : ∀ i j, dual i (q j) = if i = j then 1 else 0)
    {a : Fin (r + 1) → V} (ha : a ∈ boundarySpan (K := K) q) :
    boundaryRetraction q dual a ∈ boundarySpan (K := K) (prefixFamily q) := by
  have hle : boundarySpan (K := K) q ≤
      (boundarySpan (K := K) (prefixFamily q)).comap (boundaryRetraction q dual) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact boundaryRetraction_generator q dual hdual p
  exact hle ha

/-- A boundary with zero last coefficient restricts to an old boundary. -/
theorem prefix_mem_boundarySpan_of_last_zero (q : Fin (r + 1) → V)
    (hq : LinearIndependent K q) {a : Fin (r + 1) → V}
    (ha : a ∈ boundarySpan (K := K) q) (hlast : a (Fin.last r) = 0) :
    prefixFamily a ∈ boundarySpan (K := K) (prefixFamily q) := by
  obtain ⟨dual, hdual⟩ := Quartic.exists_coordinate_functionals q hq
  have h := boundaryRetraction_mem q dual hdual ha
  rwa [boundaryRetraction_of_last_zero q dual a hlast] at h

/-- No old relation becomes a new boundary after adjoining one independent
generator. This is the elementary intersection assertion in `pre:endpoints`. -/
theorem extendZero_mem_boundarySpan_iff (q : Fin (r + 1) → V)
    (hq : LinearIndependent K q) (a : Fin r → V) :
    extendZero (K := K) a ∈ boundarySpan (K := K) q ↔
      a ∈ boundarySpan (K := K) (prefixFamily q) := by
  constructor
  · intro ha
    have h := prefix_mem_boundarySpan_of_last_zero q hq ha (extendZero_last a)
    simpa only [prefixFamily_extendZero] using h
  · exact extendZero_mem_boundarySpan q

theorem extension_comap_boundarySpan (q : Fin (r + 1) → V)
    (hq : LinearIndependent K q) :
    (boundarySpan (K := K) q).comap extendZero =
      boundarySpan (K := K) (prefixFamily q) := by
  ext a
  exact extendZero_mem_boundarySpan_iff q hq a

/-- The actual intersection of the new boundary space with the old coefficient
space consists precisely of the extended old boundaries. -/
theorem boundarySpan_intersection_old_space (q : Fin (r + 1) → V)
    (hq : LinearIndependent K q) :
    boundarySpan (K := K) q ⊓ LinearMap.range extendZero =
      (boundarySpan (K := K) (prefixFamily q)).map extendZero := by
  ext a
  constructor
  · rintro ⟨ha, ⟨b, rfl⟩⟩
    exact ⟨b, (extendZero_mem_boundarySpan_iff q hq b).mp ha, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨extendZero_mem_boundarySpan q hb, ⟨b, rfl⟩⟩

theorem boundary_with_last_zero_is_old (q : Fin (r + 1) → V)
    (hq : LinearIndependent K q) (a : Fin (r + 1) → V)
    (ha : a ∈ boundarySpan (K := K) q) (hlast : a (Fin.last r) = 0) :
    ∃ b ∈ boundarySpan (K := K) (prefixFamily q), extendZero (K := K) b = a :=
  ⟨prefixFamily a, prefix_mem_boundarySpan_of_last_zero q hq ha hlast,
    extendZero_prefixFamily a hlast⟩

theorem old_boundaries_map_to_boundaries (q : Fin (r + 1) → V) :
    boundarySpan (K := K) (prefixFamily q) ≤
      (boundarySpan (K := K) q).comap extendZero := by
  intro a ha
  exact extendZero_mem_boundarySpan q ha

/-- The inclusion already descends to the full coefficient spaces modulo
Koszul boundaries, before restricting to multiplication kernels. -/
def coefficientQuotientExtension (q : Fin (r + 1) → V) :
    ((Fin r → V) ⧸ boundarySpan (K := K) (prefixFamily q)) →ₗ[K]
      ((Fin (r + 1) → V) ⧸ boundarySpan (K := K) q) :=
  (boundarySpan (K := K) (prefixFamily q)).mapQ (boundarySpan (K := K) q)
    extendZero (old_boundaries_map_to_boundaries q)

theorem coefficientQuotientExtension_injective (q : Fin (r + 1) → V)
    (hq : LinearIndependent K q) :
    Function.Injective (coefficientQuotientExtension (K := K) q) := by
  apply LinearMap.ker_eq_bot.mp
  rw [coefficientQuotientExtension, Submodule.ker_mapQ,
    extension_comap_boundarySpan q hq, Submodule.mkQ_map_self]

end Boundaries

section GeneralHomology

variable {K V U W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

/-- A commuting map of coefficient spaces restricts to their cycle spaces. -/
def inducedCycleMap (f : V →ₗ[K] W) (g : U →ₗ[K] W) (e : V →ₗ[K] U)
    (h : g.comp e = f) : f.ker →ₗ[K] g.ker where
  toFun a := ⟨e a.val, by
    change g (e a.val) = 0
    rw [← LinearMap.comp_apply, h]
    exact a.property⟩
  map_add' a b := by apply Subtype.ext; exact e.map_add _ _
  map_smul' c a := by apply Subtype.ext; exact e.map_smul _ _

theorem incoming_mapped (f : V →ₗ[K] W) (g : U →ₗ[K] W)
    (e : V →ₗ[K] U) (h : g.comp e = f)
    (B : Submodule K V) (B' : Submodule K U) (hB : B ≤ B'.comap e) :
    Quartic.kernelBoundary f B ≤
      (Quartic.kernelBoundary g B').comap (inducedCycleMap f g e h) := by
  intro a ha
  exact hB ha

theorem incoming_comap_eq (f : V →ₗ[K] W) (g : U →ₗ[K] W)
    (e : V →ₗ[K] U) (h : g.comp e = f)
    (B : Submodule K V) (B' : Submodule K U) (hB : B'.comap e = B) :
    (Quartic.kernelBoundary g B').comap (inducedCycleMap f g e h) =
      Quartic.kernelBoundary f B := by
  ext a
  change a.val ∈ B'.comap e ↔ a.val ∈ B
  rw [hB]

/-- The map of kernel quotients induced by a commuting coefficient map. -/
def inducedHomologyMap (f : V →ₗ[K] W) (g : U →ₗ[K] W)
    (e : V →ₗ[K] U) (h : g.comp e = f)
    (B : Submodule K V) (B' : Submodule K U) (hB : B ≤ B'.comap e) :
    Quartic.KernelModulo f B →ₗ[K] Quartic.KernelModulo g B' :=
  (Quartic.kernelBoundary f B).mapQ (Quartic.kernelBoundary g B')
    (inducedCycleMap f g e h) (incoming_mapped f g e h B B' hB)

theorem inducedHomologyMap_injective (f : V →ₗ[K] W) (g : U →ₗ[K] W)
    (e : V →ₗ[K] U) (h : g.comp e = f)
    (B : Submodule K V) (B' : Submodule K U) (hB : B ≤ B'.comap e)
    (hreflect : B'.comap e = B) :
    Function.Injective (inducedHomologyMap f g e h B B' hB) := by
  apply LinearMap.ker_eq_bot.mp
  rw [inducedHomologyMap, Submodule.ker_mapQ,
    incoming_comap_eq f g e h B B' hreflect, Submodule.mkQ_map_self]

end GeneralHomology

section Cycles

variable {K : Type*} [Field K] {n r : ℕ}

theorem quadraticMultiplication_extendZero (q : Fin (r + 1) → Quartic.Forms K n 2)
    (a : Fin r → Quartic.Forms K n 2) :
    Quartic.quadraticMultiplication q (extendZero (K := K) a) =
      Quartic.quadraticMultiplication (prefixFamily q) a := by
  simp [Quartic.quadraticMultiplication, Fin.sum_univ_castSucc, prefixFamily]

/-- An old multiplication cycle remains a cycle after appending a zero coefficient. -/
def cycleExtension (q : Fin (r + 1) → Quartic.Forms K n 2) :
    LinearMap.ker (Quartic.quadraticMultiplication (prefixFamily q)) →ₗ[K]
      LinearMap.ker (Quartic.quadraticMultiplication q) where
  toFun a := ⟨extendZero (K := K) a.val, by
    change Quartic.quadraticMultiplication q (extendZero a.val) = 0
    rw [quadraticMultiplication_extendZero]
    exact a.property⟩
  map_add' a b := by
    apply Subtype.ext
    exact (extendZero (K := K)).map_add a.val b.val
  map_smul' c a := by
    apply Subtype.ext
    exact (extendZero (K := K)).map_smul c a.val

theorem cycleExtension_injective (q : Fin (r + 1) → Quartic.Forms K n 2) :
    Function.Injective (cycleExtension q) := by
  intro a b h
  apply Subtype.ext
  exact extendZero_injective (congrArg Subtype.val h)

theorem multiplication_comp_extendZero (q : Fin (r + 1) → Quartic.Forms K n 2) :
    (Quartic.quadraticMultiplication q).comp extendZero =
      Quartic.quadraticMultiplication (prefixFamily q) := by
  apply LinearMap.ext
  intro a
  exact quadraticMultiplication_extendZero q a

/-- The actual degree-four first homology map obtained by adjoining the last
quadratic generator and extending old coefficients by zero. -/
def homologyExtension (q : Fin (r + 1) → Quartic.Forms K n 2) :
    Quartic.QuarticHomology (prefixFamily q) →ₗ[K] Quartic.QuarticHomology q :=
  inducedHomologyMap (Quartic.quadraticMultiplication (prefixFamily q))
    (Quartic.quadraticMultiplication q) extendZero (multiplication_comp_extendZero q)
    (Quartic.koszulSpace (prefixFamily q)) (Quartic.koszulSpace q)
    (old_boundaries_map_to_boundaries q)

/-- The manuscript's homology injection for one newly adjoined independent
quadratic. No characteristic-zero assumption is needed for this assertion. -/
theorem homologyExtension_injective (q : Fin (r + 1) → Quartic.Forms K n 2)
    (hq : LinearIndependent K q) : Function.Injective (homologyExtension q) := by
  apply inducedHomologyMap_injective
  exact extension_comap_boundarySpan q hq

theorem homology_prefix_finrank_le (q : Fin (r + 1) → Quartic.Forms K n 2)
    (hq : LinearIndependent K q) :
    Module.finrank K (Quartic.QuarticHomology (prefixFamily q)) ≤
      Module.finrank K (Quartic.QuarticHomology q) :=
  LinearMap.finrank_le_finrank_of_injective (homologyExtension_injective q hq)

end Cycles

end

end Quartic.EndpointHomology
