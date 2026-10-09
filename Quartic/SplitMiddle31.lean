module

public import Quartic.ThreeBlockModel
public import Quartic.MarkedCoefficient

@[expose] public section

/-!
# The actual polynomial (3,1) split block

The X variables are the three variables of the fixed pure block. Coefficients
of each Y variable are stored separately, so every map below is multiplication
of actual homogeneous X-polynomials. The cross-boundary map and multiplication
are defined explicitly; their ranks are proved, not assumed.
-/

noncomputable section

namespace Quartic.SplitMiddle31

set_option maxHeartbeats 2000000

open Module MvPolynomial ThreeBlockModel

section GeneralProjection

variable {K V W Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z]

/-- A coefficient projection vanishing on boundaries descends to homology. -/
def quotientProjection (f : V →ₗ[K] W) (B : Submodule K V) (p : V →ₗ[K] Z)
    (hB : B ≤ p.ker) : KernelModulo f B →ₗ[K] Z :=
  (kernelBoundary f B).liftQ (p.comp f.ker.subtype) (by
    intro a ha
    exact hB ha)

theorem quotientProjection_injective (f : V →ₗ[K] W) (B : Submodule K V) (p : V →ₗ[K] Z)
    (hB : B ≤ p.ker) (hker : ∀ a, f a = 0 → p a = 0 → a ∈ B) :
    Function.Injective (quotientProjection f B p hB) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro a ha
  exact hker a.val a.property ha

end GeneralProjection

variable (K : Type*) [Field K] (m c : ℕ)

abbrev Mixed := Fin c → Fin m → Forms K 3 1
abbrev Source := (Fin c → Forms K 3 2) × (Fin 4 → Fin m → Forms K 3 1)
abbrev Target := Fin m → Forms K 3 3
abbrev BoundarySource := Fin 4 → Fin c → K

/-- Multiplication by the four actual pure block quadrics on linear coefficients. -/
def pureCubic : (Fin 4 → Forms K 3 1) →ₗ[K] Forms K 3 3 where
  toFun b := ⟨∑ i, (blockQuadrics i).val * (b i).val,
    (Forms K 3 3).sum_mem fun i _ => (blockQuadrics i).property.mul (b i).property⟩
  map_add' b d := by apply Subtype.ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a b := by apply Subtype.ext; simp [← Finset.smul_sum]

variable {K m c}

theorem pureCubic_surjective : Function.Surjective (pureCubic K) := by
  have hrange : LinearMap.range ((Forms K 3 3).subtype.comp (pureCubic K)) =
      blockSpace (K := K) * Forms K 3 1 := by
    apply le_antisymm
    · rintro p ⟨b, rfl⟩
      change (∑ i, (blockQuadrics i).val * (b i).val) ∈ _
      apply Submodule.sum_mem
      intro i _
      exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (b i).property
    · apply Submodule.mul_le.mpr
      intro f hf a ha
      obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
      refine ⟨fun i => s i • (⟨a, ha⟩ : Forms K 3 1), ?_⟩
      change (pureCubic K (fun i => s i • (⟨a, ha⟩ : Forms K 3 1))).val = _
      simp [pureCubic, blockQuadrics, Finset.sum_mul]
  intro p
  have hp : p.val ∈ LinearMap.range ((Forms K 3 3).subtype.comp (pureCubic K)) := by
    rw [hrange, cubic_products_eq]
    exact p.property
  obtain ⟨b, hb⟩ := hp
  exact ⟨b, Subtype.ext hb⟩

/-- The mixed-generator component in bidegree (3,1). -/
def mixedMultiplication (g : Mixed K m c) : (Fin c → Forms K 3 2) →ₗ[K] Target K m where
  toFun a l := ⟨∑ j, (a j).val * (g j l).val,
    (Forms K 3 3).sum_mem fun j _ => (a j).property.mul (g j l).property⟩
  map_add' a b := by ext l : 1; apply Subtype.ext; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a b := by ext l : 1; apply Subtype.ext; simp [← Finset.smul_sum]

/-- The pure-generator component in bidegree (3,1). -/
def pureMultiplication : (Fin 4 → Fin m → Forms K 3 1) →ₗ[K] Target K m where
  toFun b l := pureCubic K (fun i => b i l)
  map_add' b d := by ext l; simp [pureCubic, mul_add, Finset.sum_add_distrib]
  map_smul' a b := by ext l; simp [pureCubic, ← Finset.smul_sum]

/-- The complete polynomial multiplication map for the (3,1) coefficient types. -/
def multiplication (g : Mixed K m c) : Source K m c →ₗ[K] Target K m :=
  (mixedMultiplication g).coprod pureMultiplication

/-- Incoming Koszul boundaries between a pure generator and a mixed generator. -/
def boundary (g : Mixed K m c) : BoundarySource K c →ₗ[K] Source K m c where
  toFun t := (fun j => ∑ i, t i j • blockQuadrics i,
    fun i l => -(∑ j, t i j • g j l))
  map_add' t s := by ext <;> simp [add_smul, Finset.sum_add_distrib, add_comm]
  map_smul' a t := by ext <;> simp [mul_smul, Finset.smul_sum, smul_neg]

@[simp] theorem boundary_fst (g : Mixed K m c) (t : BoundarySource K c) (j : Fin c) :
    (boundary g t).1 j = ∑ i, t i j • blockQuadrics i := rfl

@[simp] theorem boundary_snd (g : Mixed K m c) (t : BoundarySource K c) (i : Fin 4) (l : Fin m) :
    (boundary g t).2 i l = -(∑ j, t i j • g j l) := rfl

theorem boundary_injective (g : Mixed K m c) : Function.Injective (boundary g) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro t ht
  funext i j
  have hj : (∑ i, t i j • blockQuadrics (K := K) i) = 0 :=
    congrArg (fun a : Source K m c => a.1 j) ht
  exact Fintype.linearIndependent_iff.mp blockQuadrics_independent (fun i => t i j) hj i

@[simp] theorem multiplication_boundary (g : Mixed K m c) (t : BoundarySource K c) :
    multiplication g (boundary g t) = 0 := by
  funext l
  apply Subtype.ext
  change (mixedMultiplication g (boundary g t).1 l).val +
    (pureCubic K (fun i => (boundary g t).2 i l)).val = 0
  simp only [mixedMultiplication, pureCubic, boundary, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_neg,
    Finset.sum_mul, Finset.mul_sum, mul_neg, smul_mul_assoc, mul_smul_comm]
  rw [Finset.sum_comm]
  simp only [Finset.sum_neg_distrib, add_neg_cancel]

theorem boundary_range_le_kernel (g : Mixed K m c) :
    LinearMap.range (boundary g) ≤ LinearMap.ker (multiplication g) := by
  rintro _ ⟨t, rfl⟩
  exact multiplication_boundary g t

theorem multiplication_surjective (g : Mixed K m c) : Function.Surjective (multiplication g) := by
  intro p
  choose b hb using fun l => pureCubic_surjective (K := K) (p l)
  refine ⟨(0, fun i l => b l i), ?_⟩
  funext l
  change (mixedMultiplication g 0) l + pureCubic K (fun i => b l i) = p l
  rw [map_zero]
  exact (zero_add _).trans (hb l)

/-- The homology of this actual bidegree block. -/
abbrev Homology (g : Mixed K m c) :=
  KernelModulo (multiplication g) (LinearMap.range (boundary g))

theorem boundary_finrank (g : Mixed K m c) :
    finrank K (LinearMap.range (boundary g)) = 4 * c := by
  rw [LinearMap.finrank_range_of_inj (boundary_injective g)]
  simp [BoundarySource, Module.finrank_pi_fintype]

/-- The uniform (3,1) entry of the split-complex homology inventory. -/
theorem homology_finrank (g : Mixed K m c) : finrank K (Homology g) = 2 * m + 2 * c := by
  have hhom := finrank_kernelModulo_add (multiplication g) (LinearMap.range (boundary g))
  have hb : finrank K (kernelBoundary (multiplication g) (LinearMap.range (boundary g))) = 4 * c := by
    unfold kernelBoundary
    rw [(Submodule.comapSubtypeEquivOfLe (boundary_range_le_kernel g)).finrank_eq]
    exact boundary_finrank g
  rw [hb] at hhom
  have hrank := (multiplication g).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (multiplication_surjective g), finrank_top] at hrank
  have hsource : finrank K (Source K m c) = 6 * c + 12 * m := by
    simp [Source, Module.finrank_pi_fintype, Module.finrank_prod, finrank_forms, Nat.choose]
    ring
  have htarget : finrank K (Target K m) = 10 * m := by
    simp [Target, Module.finrank_pi_fintype, finrank_forms, Nat.choose]
    omega
  rw [hsource, htarget] at hrank
  change finrank K (Homology g) + 4 * c = _ at hhom
  omega


/-- The mixed-generator subspace of actual (1,1) coefficient arrays. -/
def mixedSpace (g : Mixed K m c) : Submodule K (Fin m → Forms K 3 1) :=
  Submodule.span K (Set.range g)

/-- Four pure-generator coefficients, each reduced modulo the mixed space. -/
def coefficientProjection (g : Mixed K m c) :
    Source K m c →ₗ[K] (Fin 4 → ((Fin m → Forms K 3 1) ⧸ mixedSpace g)) :=
  (LinearMap.pi fun i => (mixedSpace g).mkQ.comp (LinearMap.proj i)).comp
    (LinearMap.snd K _ _)

@[simp] theorem coefficientProjection_apply (g : Mixed K m c) (a : Source K m c) (i : Fin 4) :
    coefficientProjection g a i = (mixedSpace g).mkQ (a.2 i) := rfl

theorem boundary_snd_vector (g : Mixed K m c) (t : BoundarySource K c) (i : Fin 4) :
    (boundary g t).2 i = -(∑ j, t i j • g j) := by
  funext l
  simp [boundary]

@[simp] theorem coefficientProjection_boundary (g : Mixed K m c) (t : BoundarySource K c) :
    coefficientProjection g (boundary g t) = 0 := by
  funext i
  rw [coefficientProjection_apply, boundary_snd_vector]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Reading pure coefficients on the actual polynomial cycle space. -/
def coefficientOnCycles (g : Mixed K m c) :
    (multiplication g).ker →ₗ[K] (Fin 4 → ((Fin m → Forms K 3 1) ⧸ mixedSpace g)) :=
  (coefficientProjection g).comp (multiplication g).ker.subtype

theorem boundary_le_trace_kernel (g : Mixed K m c) :
    kernelBoundary (multiplication g) (LinearMap.range (boundary g)) ≤
      LinearMap.ker (coefficientOnCycles g) := by
  intro a ha
  obtain ⟨t, ht⟩ := ha
  change coefficientProjection g a.val = 0
  change boundary g t = a.val at ht
  rw [← ht]
  exact coefficientProjection_boundary g t

theorem boundary_range_le_projection_kernel (g : Mixed K m c) :
    LinearMap.range (boundary g) ≤ LinearMap.ker (coefficientProjection g) := by
  rintro _ ⟨t, rfl⟩
  exact coefficientProjection_boundary g t

/-- The full (3,1) trace on homology, including the pure cubic-kernel classes. -/
def trace (g : Mixed K m c) :
    Homology g →ₗ[K] (Fin 4 → ((Fin m → Forms K 3 1) ⧸ mixedSpace g)) :=
  quotientProjection (multiplication g) (LinearMap.range (boundary g))
    (coefficientProjection g) (boundary_range_le_projection_kernel g)

/-- A cycle whose pure coefficients lie in the mixed space is a cross-boundary,
provided multiplication by the mixed generators is injective in this bidegree. -/
theorem coefficient_kernel_is_boundary (g : Mixed K m c)
    (hinj : Function.Injective (mixedMultiplication g)) (a : Source K m c)
    (hcycle : multiplication g a = 0)
    (hcoeff : coefficientProjection g a = 0) : a ∈ LinearMap.range (boundary g) := by
  have hmem (i : Fin 4) : a.2 i ∈ mixedSpace g := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrFun hcoeff i
  choose t ht using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hmem i)
  let b := boundary g (-t)
  have hsnd : b.2 = a.2 := by
    funext i
    rw [show b.2 i = (boundary g (-t)).2 i from rfl, boundary_snd_vector]
    change -(∑ j, (-(t i j)) • g j) = a.2 i
    rw [← Finset.sum_neg_distrib]
    calc
      ∑ j, -((-(t i j)) • g j) = ∑ j, t i j • g j := by
        apply Finset.sum_congr rfl
        intro j _
        have hn : (-(t i j)) • g j = -(t i j • g j) := _root_.neg_smul (t i j) (g j)
        rw [hn, neg_neg]
      _ = a.2 i := ht i
  have hz : multiplication g (a - b) = 0 := by
    rw [map_sub, hcycle]
    have hb : multiplication g b = 0 := multiplication_boundary g (-t)
    rw [hb, sub_self]
  have hpure : pureMultiplication (K := K) (m := m) (a.2 - b.2) = 0 := by
    rw [hsnd, sub_self, map_zero]
  change mixedMultiplication g (a.1 - b.1) + pureMultiplication (a.2 - b.2) = 0 at hz
  rw [hpure, add_zero] at hz
  have hfst : a.1 = b.1 := by
    have ha : a.1 - b.1 = 0 := hinj (hz.trans (map_zero _).symm)
    exact sub_eq_zero.mp ha
  refine ⟨-t, ?_⟩
  change b = a
  exact Prod.ext hfst.symm hsnd

/-- Uniform algebraic trace injection from `tb:k31injective`. Its injectivity
hypothesis has an explicit separated-variable witness below. -/
theorem trace_injective (g : Mixed K m c)
    (hinj : Function.Injective (mixedMultiplication g)) : Function.Injective (trace g) := by
  exact quotientProjection_injective (multiplication g) (LinearMap.range (boundary g))
    (coefficientProjection g) (boundary_range_le_projection_kernel g)
    (coefficient_kernel_is_boundary g hinj)

/-- Further quotient the four coefficient traces by a prescribed subspace. -/
def traceModulo (g : Mixed K m c)
    (D : Submodule K ((Fin m → Forms K 3 1) ⧸ mixedSpace g)) :
    Homology g →ₗ[K] (Fin 4 → (((Fin m → Forms K 3 1) ⧸ mixedSpace g) ⧸ D)) where
  toFun a i := D.mkQ (trace g a i)
  map_add' a b := by funext i; simp
  map_smul' t a := by funext i; simp

/-- Uniform rank loss after quotienting each of the four trace coordinates.
This is the quantitative conclusion of `tb:k31injective`. -/
theorem traceModulo_rank_bound (g : Mixed K m c)
    (hinj : Function.Injective (mixedMultiplication g))
    (D : Submodule K ((Fin m → Forms K 3 1) ⧸ mixedSpace g)) :
    2 * m + 2 * c ≤ finrank K (LinearMap.range (traceModulo g D)) + 4 * finrank K D := by
  let J : (traceModulo g D).ker →ₗ[K] (Fin 4 → D) :=
    { toFun := fun a i => ⟨trace g a.val i, by
        apply (Submodule.Quotient.mk_eq_zero D).mp
        exact congrFun a.property i⟩
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        exact congrFun ((trace g).map_add a.val b.val) i
      map_smul' := by
        intro t a
        funext i
        apply Subtype.ext
        exact congrFun ((trace g).map_smul t a.val) i }
  have hJ : Function.Injective J := by
    intro a b hab
    apply Subtype.ext
    apply trace_injective g hinj
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  have hker := LinearMap.finrank_le_finrank_of_injective hJ
  have hrank := (traceModulo g D).finrank_range_add_finrank_ker
  rw [homology_finrank g] at hrank
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hker
  omega

/-- One nonzero X-linear form, used to separate the Y coefficients. -/
def coordinateX : Forms K 3 1 := ⟨X 0, isHomogeneous_X K 0⟩

/-- The uniform witness `gⱼ = x yⱼ`, for every `c ≤ m`. -/
def separatedMixed (hcm : c ≤ m) : Mixed K m c :=
  fun j l => if l = Fin.castLE hcm j then coordinateX else 0

theorem separatedMixed_injective (hcm : c ≤ m) :
    Function.Injective (mixedMultiplication (separatedMixed (K := K) hcm)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  funext j
  apply Subtype.ext
  have hj := congrArg (fun p : Target K m => (p (Fin.castLE hcm j)).val) ha
  have heq (i : Fin c) : Fin.castLE hcm j = Fin.castLE hcm i ↔ i = j := by
    rw [Fin.castLE_inj]
    exact eq_comm
  have hproduct : (a j).val * (X (0 : Fin 3) : Poly K 3) = 0 := by
    simpa [mixedMultiplication, separatedMixed, coordinateX, heq, apply_ite] using hj
  exact (mul_eq_zero.mp hproduct).resolve_right (X_ne_zero (0 : Fin 3))

theorem separated_trace_injective (hcm : c ≤ m) :
    Function.Injective (trace (separatedMixed (K := K) hcm)) :=
  trace_injective _ (separatedMixed_injective hcm)

/-- The mixed generators in the separated witness are independent as actual
bidegree-(1,1) polynomial coefficient arrays. -/
theorem separatedMixed_independent (hcm : c ≤ m) :
    LinearIndependent K (separatedMixed (K := K) hcm) := by
  apply Fintype.linearIndependent_iff.mpr
  intro t ht j
  have hj := congrArg (fun p : Fin m → Forms K 3 1 =>
    (p (Fin.castLE hcm j)).val.coeff (Finsupp.single 0 1)) ht
  have heq (i : Fin c) : Fin.castLE hcm j = Fin.castLE hcm i ↔ i = j := by
    rw [Fin.castLE_inj]
    exact eq_comm
  simpa [separatedMixed, coordinateX, heq, MvPolynomial.X] using hj

end Quartic.SplitMiddle31
