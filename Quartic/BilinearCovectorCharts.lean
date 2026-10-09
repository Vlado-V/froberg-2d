module

public import Quartic.BilinearImage
public import Quartic.ProjectiveKernelCharts

@[expose] public section

/-!
# Actual polynomial covector equations on subspace charts

For each graph chart of d-planes, the matrix below cuts out covectors
annihilating all bilinear products with that plane. Its rank is exactly the
actual product-image dimension. Projective kernel charts therefore cover the
nonzero annihilating covectors with the expected parameter count.
-/
noncomputable section
namespace Quartic.BilinearCovectorCharts
open Module Matrix MvPolynomial SubspaceCharts KernelPolynomialCharts
variable {K : Type*} [Field K] {a b T d : ℕ}

abbrev GraphParameters (j : Fin d ↪ Fin a) := Outside j × Fin d

def graphCoefficients (j : Fin d ↪ Fin a) (p : GraphParameters j → K) : SubspaceCharts.Parameters K j :=
  fun k i => p (k,i)

def graphVector (j : Fin d ↪ Fin a) (p : GraphParameters j → K) (i : Fin d) : Fin a → K :=
  chartLift j (graphCoefficients j p) (Pi.single i 1)

def graphPolynomial (j : Fin d ↪ Fin a) (i : Fin d) (k : Fin a) :
    MvPolynomial (GraphParameters j) K := by
  classical
  exact if hk : k ∈ Set.range j then C ((Pi.single i (1 : K) : Fin d → K) (Classical.choose hk))
    else X (⟨k,hk⟩,i)

@[simp] theorem eval_graphPolynomial (j : Fin d ↪ Fin a) (p : GraphParameters j → K)
    (i : Fin d) (k : Fin a) : eval p (graphPolynomial j i k) = graphVector j p i k := by
  classical
  by_cases hk : k ∈ Set.range j
  · obtain ⟨l,rfl⟩ := hk
    have hl : j l ∈ Set.range j := ⟨l,rfl⟩
    simp [graphPolynomial, hl, graphVector]
  · simp [graphPolynomial, hk, graphVector, chartLift_outside j _ _ ⟨k,hk⟩,
      parameterMap_apply, graphCoefficients, Pi.single_apply]

 theorem graphVector_span (j : Fin d ↪ Fin a) (p : GraphParameters j → K) :
    Submodule.span K (Set.range (graphVector j p)) = chartSubspace j (graphCoefficients j p) := by
  classical
  have hfun : graphVector j p = chartLift j (graphCoefficients j p) ∘ Pi.basisFun K (Fin d) := by
    funext i
    simp [graphVector, Pi.basisFun_apply]
  rw [hfun, Set.range_comp, ← Submodule.map_span, (Pi.basisFun K (Fin d)).span_eq,
    Submodule.map_top]
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact chartLift_mem _ _ _
  · intro x hx
    refine ⟨chartEquiv j (graphCoefficients j p) ⟨x,hx⟩, ?_⟩
    exact congrArg Subtype.val ((chartEquiv j (graphCoefficients j p)).symm_apply_apply ⟨x,hx⟩)

/-- Rows are the products of each scalar coefficient basis vector with each
graph basis vector. Columns are covector coordinates. -/
def constraint (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (j : Fin d ↪ Fin a) :
    Matrix (Fin (d*b)) (Fin T) (MvPolynomial (GraphParameters j) K) :=
  fun l k => ∑ h : Fin a, graphPolynomial j (finProdFinEquiv.symm l).1 h *
    C (mu (Pi.single (finProdFinEquiv.symm l).2 1) (Pi.single h 1) k)

 theorem eval_constraint (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (j : Fin d ↪ Fin a) (p : GraphParameters j → K) (l : Fin (d*b)) (k : Fin T) :
    evaluated (constraint mu j) p l k =
      mu (Pi.single (finProdFinEquiv.symm l).2 1) (graphVector j p (finProdFinEquiv.symm l).1) k := by
  classical
  change eval p (constraint mu j l k) = _
  conv_rhs => rw [← (Pi.basisFun K (Fin a)).sum_equivFun (graphVector j p (finProdFinEquiv.symm l).1)]
  simp [constraint, Pi.basisFun_apply, Pi.basisFun_equivFun, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The constraint rank is the actual bilinear-image dimension of the d-plane. -/
theorem constraint_rank (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (j : Fin d ↪ Fin a) (p : GraphParameters j → K) :
    (evaluated (constraint mu j) p).rank =
      finrank K (BilinearImage.image mu (chartSubspace j (graphCoefficients j p))) := by
  classical
  rw [← Matrix.rank_transpose, Matrix.rank_eq_finrank_span_cols, ← graphVector_span j p,
    BilinearImage.image_span_basis (Pi.basisFun K (Fin b))]
  have hset : Set.range (evaluated (constraint mu j) p).transpose.col =
      Set.range (fun z : Fin d × Fin b => mu ((Pi.basisFun K (Fin b)) z.2) (graphVector j p z.1)) := by
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      refine ⟨finProdFinEquiv.symm l, ?_⟩
      funext k
      simpa only [Matrix.col_apply, Matrix.transpose_apply, Pi.basisFun_apply] using
        (eval_constraint mu j p l k).symm
    · rintro ⟨⟨i,h⟩,rfl⟩
      refine ⟨finProdFinEquiv (i,h), ?_⟩
      funext k
      simpa only [Equiv.symm_apply_apply, Pi.basisFun_apply, Matrix.col_apply, Matrix.transpose_apply] using
        eval_constraint mu j p (finProdFinEquiv (i,h)) k
  rw [hset]

/-- The actual functional represented by a finite covector coordinate array. -/
def covector (ell : Fin T → K) : (Fin T → K) →ₗ[K] K :=
  ∑ k, ell k • LinearMap.proj k

@[simp] theorem covector_apply (ell x : Fin T → K) : covector ell x = ∑ k, ell k * x k := by
  simp [covector, smul_eq_mul]

 theorem constraint_mulVec (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (j : Fin d ↪ Fin a) (p : GraphParameters j → K) (ell : Fin T → K) (l : Fin (d*b)) :
    (evaluated (constraint mu j) p *ᵥ ell) l = covector ell
      (mu (Pi.single (finProdFinEquiv.symm l).2 1) (graphVector j p (finProdFinEquiv.symm l).1)) := by
  simp only [Matrix.mulVec, dotProduct, eval_constraint, covector_apply, mul_comm]

/-- The matrix kernel is exactly the actual product-image annihilator. -/
theorem constraint_kernel_iff (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (j : Fin d ↪ Fin a) (p : GraphParameters j → K) (ell : Fin T → K) :
    evaluated (constraint mu j) p *ᵥ ell = 0 ↔
      BilinearImage.image mu (chartSubspace j (graphCoefficients j p)) ≤ LinearMap.ker (covector ell) := by
  classical
  rw [← graphVector_span j p, BilinearImage.image_span_basis (Pi.basisFun K (Fin b))]
  constructor
  · intro hz
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,h⟩,rfl⟩
    change covector ell (mu ((Pi.basisFun K (Fin b)) h) (graphVector j p i)) = 0
    have he := congrFun hz (finProdFinEquiv (i,h))
    rw [constraint_mulVec] at he
    simpa only [Equiv.symm_apply_apply, Pi.zero_apply, Pi.basisFun_apply] using he
  · intro h
    funext l
    rw [constraint_mulVec]
    exact h (Submodule.subset_span ⟨finProdFinEquiv.symm l, by simp only [Pi.basisFun_apply]⟩)

/-- Coordinate arrays faithfully represent covectors. -/
theorem covector_injective : Function.Injective (covector (K := K) (T := T)) := by
  classical
  intro x y h
  funext k
  have he := LinearMap.congr_fun h (Pi.single k 1)
  simpa [covector_apply, Pi.single_apply] using he

/-- Finite chart choices: a graph selector, a nonsingular minor, and a free
covector coordinate normalized to one. -/
abbrev ChartType (a b T d e : ℕ) :=
  (_j : Fin d ↪ Fin a) × (Fin e ↪ Fin (d*b)) ×
    (v : Fin e ↪ Fin T) × Outside v

abbrev Parameters {e : ℕ} (c : ChartType a b T d e) :=
  ProjectiveKernelCharts.Parameters (GraphParameters c.1) c.2.2.1 c.2.2.2

/-- The rational covector numerator of the actual bilinear annihilator chart. -/
def numerator (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    {e : ℕ} (c : ChartType a b T d e) : Fin T → MvPolynomial (Parameters c) K :=
  ProjectiveKernelCharts.numerator (constraint mu c.1) c.2.1 c.2.2.1 c.2.2.2

def denominator (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    {e : ℕ} (c : ChartType a b T d e) : MvPolynomial (Parameters c) K :=
  ProjectiveKernelCharts.denominator (constraint mu c.1) c.2.1 c.2.2.1 c.2.2.2

/-- The graph subspace encoded by the same chart parameters as its covector. -/
def subspace {e : ℕ} (c : ChartType a b T d e) (p : Parameters c → K) : Submodule K (Fin a → K) :=
  chartSubspace c.1 (graphCoefficients c.1 (fun i => p (Sum.inl i)))

/-- Exact projective parameter count, with e the chosen image rank bound. -/
theorem parameter_count {e : ℕ} (c : ChartType a b T d e) :
    Fintype.card (Parameters c) = d*(a-d) + (T-e) - 1 := by
  rw [ProjectiveKernelCharts.parameter_count, card_coefficient_positions]

/-- Every actual nonzero annihilating covector lies on a rational chart,
with the original subspace encoded by the same parameters. -/
theorem cover_annihilator (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    {e : ℕ} (S : Submodule K (Fin a → K)) (hS : finrank K S = d)
    (himage : e ≤ finrank K (BilinearImage.image mu S))
    (ell : Fin T → K) (hnz : ell ≠ 0)
    (hann : BilinearImage.image mu S ≤ LinearMap.ker (covector ell)) :
    ∃ c : ChartType a b T d e, ∃ p : Parameters c → K, ∃ s : K,
      s ≠ 0 ∧ subspace c p = S ∧ eval p (denominator mu c) ≠ 0 ∧
        ell = s • RationalImageAvoidance.rationalMap (numerator mu c) (denominator mu c) p := by
  classical
  obtain ⟨j,A,hA⟩ := SubspaceCharts.exists_chart S hS
  let t : GraphParameters j → K := fun z => A z.1 z.2
  have hgraph : graphCoefficients j t = A := rfl
  have hrank : e ≤ (evaluated (constraint mu j) t).rank := by
    rw [constraint_rank, hgraph, hA]
    exact himage
  obtain ⟨u,v,hdet⟩ := KernelCharts.exists_minor_of_rank_le (evaluated (constraint mu j) t) hrank
  have hker : evaluated (constraint mu j) t *ᵥ ell = 0 := by
    rw [constraint_kernel_iff, hgraph, hA]
    exact hann
  obtain ⟨z,p,s,hs,hp,hden,he⟩ :=
    ProjectiveKernelCharts.cover_nonzero_kernel (constraint mu j) u v t hdet ell hker hnz
  refine ⟨⟨j,u,v,z⟩,p,s,hs,?_,hden,he⟩
  change chartSubspace j (graphCoefficients j (fun i => p (Sum.inl i))) = S
  have ht : (fun i => p (Sum.inl i)) = t := funext hp
  rw [ht,hgraph,hA]

end Quartic.BilinearCovectorCharts
