module

public import Quartic.PolynomialSubspaceCovectorCharts
public import Quartic.ProfileChartBound

@[expose] public section

/-!
# Actual iterated profile charts as covector-incidence inputs

This module flattens the ordered blocks into ordinary finite coordinates,
identifies the polynomial graph-vector span with the actual iterated chart,
and applies shared-coefficient avoidance to its prescribed prefix profile.
-/

noncomputable section
namespace Quartic.IteratedCovectorCharts
open Module Matrix MvPolynomial IteratedBlockCharts
open BilinearCovectorCharts (covector)
open BilinearCoefficientKernel
variable {K : Type*} [Field K] {n : ℕ} {b r : Fin n → ℕ}

def indexEquiv (b : Fin n → ℕ) : ((i : Fin n) × Fin (b i)) ≃ Fin (∑ i,b i) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Actual flattening of the block coordinates. -/
def coordinates (K : Type*) [Field K] (b : Fin n → ℕ) :
    Ambient K b ≃ₗ[K] (Fin (∑ i,b i) → K) where
  toFun x k := x ((indexEquiv b).symm k).1 ((indexEquiv b).symm k).2
  invFun x i k := x (indexEquiv b ⟨i,k⟩)
  left_inv x := by
    funext i k
    exact congrArg (fun z : (i : Fin n) × Fin (b i) => x z.1 z.2)
      ((indexEquiv b).symm_apply_apply ⟨i,k⟩)
  right_inv x := by funext k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Polynomial graph vectors in the finite coordinates expected by covector charts. -/
def graphPolynomial (j : Selectors b r) (h : Fin (∑ i,r i)) (k : Fin (∑ i,b i)) :
    MvPolynomial (ParameterIndex j) K :=
  liftPolynomial j (basisVector ((indexEquiv r).symm h).1 ((indexEquiv r).symm h).2)
    ((indexEquiv b).symm k).1 ((indexEquiv b).symm k).2

theorem evaluated_graphVector (j : Selectors b r) (p : Parameters K j) (h : Fin (∑ i,r i)) :
    PolynomialSubspaceCovectorCharts.vector (graphPolynomial j) p h=
      coordinates K b (lift j p (basisVector ((indexEquiv r).symm h).1 ((indexEquiv r).symm h).2)) := by
  funext k
  exact eval_liftPolynomial _ _ _ _ _

theorem enumerated_basis_span :
    Submodule.span K (Set.range (fun h : Fin (∑ i,r i) =>
      (basisVector ((indexEquiv r).symm h).1 ((indexEquiv r).symm h).2 : Ambient K r)))=⊤ := by
  apply top_unique
  intro x _
  rw [coordinate_expansion x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨indexEquiv r ⟨i,a⟩,
    congrArg (fun z : (i : Fin n) × Fin (r i) => basisVector (K := K) z.1 z.2)
      ((indexEquiv r).symm_apply_apply ⟨i,a⟩)⟩

/-- The covector module's spanned subspace is exactly the flattened actual chart. -/
theorem subspace_graphPolynomial (j : Selectors b r) (p : Parameters K j) :
    PolynomialSubspaceCovectorCharts.subspace (graphPolynomial j) p=
      (chart j p).map (coordinates K b).toLinearMap := by
  have hfun : PolynomialSubspaceCovectorCharts.vector (graphPolynomial j) p=
      ((coordinates K b).toLinearMap.comp (lift j p)) ∘
        (fun h : Fin (∑ i,r i) => basisVector ((indexEquiv r).symm h).1 ((indexEquiv r).symm h).2) :=
    funext (evaluated_graphVector j p)
  rw [PolynomialSubspaceCovectorCharts.subspace,hfun,Set.range_comp,← Submodule.map_span,
    enumerated_basis_span,Submodule.map_top,LinearMap.range_comp]
  rfl

/-- Actual prefix ranks imply coverage by the literal polynomial vector family. -/
theorem covered_of_profile (S : Submodule K (Fin (∑ i,b i) → K))
    (hprofile : ∀ i,finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
      (S.comap (coordinates K b).toLinearMap) i)=r i) :
    PolynomialSubspaceCovectorCharts.Covered (fun j : Selectors b r => graphPolynomial j) S := by
  obtain ⟨j,p,hp⟩ := IteratedBlockCharts.exists_chart (S.comap (coordinates K b).toLinearMap) hprofile
  refine ⟨j,p,?_⟩
  rw [subspace_graphPolynomial,hp]
  exact Submodule.map_comap_eq_of_surjective (coordinates K b).surjective S

theorem finrank_of_profile (S : Submodule K (Fin (∑ i,b i) → K))
    (hprofile : ∀ i,finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
      (S.comap (coordinates K b).toLinearMap) i)=r i) : finrank K S=∑ i,r i := by
  obtain ⟨j,p,hp⟩ := IteratedBlockCharts.exists_chart (S.comap (coordinates K b).toLinearMap) hprofile
  have hmap : (chart j p).map (coordinates K b).toLinearMap=S := by
    rw [hp]
    exact Submodule.map_comap_eq_of_surjective (coordinates K b).surjective S
  rw [← hmap,LinearEquiv.finrank_map_eq,chart_finrank]

/-- A negative conditioned count excludes covectors with the actual specified
prefix profile. No independent model of the profile stratum is assumed. -/
theorem principal_open_excludes_profile [Infinite K] {B T e q : ℕ}
    (mu : (Fin B → K) →ₗ[K] (Fin (∑ i,b i) → K) →ₗ[K] (Fin T → K))
    (hcount : parameterCount b r+(T-e)-1 < q*((∑ i,b i)-(∑ i,r i))) :
    ∃ P : MvPolynomial (Fin q × Fin B) K,
      (∃ Q : Fin q × Fin B → K,eval Q P ≠ 0) ∧
      ∀ Q,eval Q P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        (∀ i,finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
          ((LinearMap.ker (relationMap mu ell)).comap (coordinates K b).toLinearMap) i)=r i) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ∃ j : Fin q,∃ v : Fin (∑ i,b i) → K,covector ell (mu (fun k => Q (j,k)) v) ≠ 0 := by
  classical
  obtain ⟨P,hP,hgood⟩ := PolynomialSubspaceCovectorCharts.principal_open_excludes_covered_stratum
    (d := ∑ i,r i) (e := e) mu (fun j : Selectors b r => graphPolynomial j)
    (by intro j; rw [parameter_count]; exact hcount)
  refine ⟨P,hP,?_⟩
  intro Q hQ ell hell hprofile himage
  exact hgood Q hQ ell hell (finrank_of_profile _ hprofile) (covered_of_profile _ hprofile) himage

/-- The same actual-profile exclusion accepts a compressed integer upper
bound for chart parameters, including an empty full-image covector stratum. -/
theorem principal_open_excludes_profile_of_int_bound [Infinite K] {B T e q : ℕ}
    (mu : (Fin B → K) →ₗ[K] (Fin (∑ i,b i) → K) →ₗ[K] (Fin T → K))
    (g : ℤ) (hg : (parameterCount b r:ℤ) ≤ g)
    (hcount : g+(T:ℤ)-(e:ℤ)-1 < (q*((∑ i,b i)-(∑ i,r i)):ℕ)) :
    ∃ P : MvPolynomial (Fin q × Fin B) K,
      (∃ Q : Fin q × Fin B → K,eval Q P ≠ 0) ∧
      ∀ Q,eval Q P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        (∀ i,finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
          ((LinearMap.ker (relationMap mu ell)).comap (coordinates K b).toLinearMap) i)=r i) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ∃ j : Fin q,∃ v : Fin (∑ i,b i) → K,covector ell (mu (fun k => Q (j,k)) v) ≠ 0 := by
  classical
  obtain ⟨P,hP,hgood⟩ := PolynomialSubspaceCovectorCharts.principal_open_excludes_covered_stratum_of_int_bound
    (d := ∑ i,r i) (e := e) mu (fun j : Selectors b r => graphPolynomial j) g
    (by intro j; rw [parameter_count]; exact hg) hcount
  refine ⟨P,hP,?_⟩
  intro Q hQ ell hell hprofile himage
  exact hgood Q hQ ell hell (finrank_of_profile _ hprofile) (covered_of_profile _ hprofile) himage

open ProfileChartBound ProfileCertificate LayerRankCounts

theorem sum_blockDimensions (m c : ℕ) :
    (∑ k,blockDimensions (coreA c) (freeW m c) k)=totalA m c := by
  simp [blockDimensions,Fin.sum_univ_succ,totalA,mul_comm]

theorem sum_blockRanks {w : ℕ} (i : ℕ) (r : Fin w → ℕ) (hr : ∀ k,r k ≤ 3) :
    (∑ k,blockRanks i r k)=profileDim i (levelCount r 1) (levelCount r 2) (levelCount r 3) := by
  simp only [blockRanks,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,rank_sum_nat_eq_layers r hr,profileDim]
  omega

/-- The manuscript's compressed Cell count now excludes the actual covered
profile stratum whenever its conditioned count is negative. -/
theorem principal_open_excludes_Cell_profile [Infinite K] {B T e q : ℕ}
    (m c i : ℕ) (hi : i ≤ coreA c) (r : Fin (freeW m c) → ℕ) (hr : ∀ k,r k ≤ 3)
    (mu : (Fin B → K) →ₗ[K]
      (Fin (∑ k,blockDimensions (coreA c) (freeW m c) k) → K) →ₗ[K] (Fin T → K))
    (hcount : Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3)+
      (T:ℤ)-(e:ℤ)-1 < (q*(totalA m c-profileDim i (levelCount r 1) (levelCount r 2) (levelCount r 3)):ℕ)) :
    ∃ P : MvPolynomial (Fin q × Fin B) K,
      (∃ Q : Fin q × Fin B → K,eval Q P ≠ 0) ∧
      ∀ Q,eval Q P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        (∀ k,finrank K (FilteredImage.initialPiece
          (fun k => Fin (blockDimensions (coreA c) (freeW m c) k) → K)
          ((LinearMap.ker (relationMap mu ell)).comap
            (coordinates K (blockDimensions (coreA c) (freeW m c))).toLinearMap) k)=blockRanks i r k) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ∃ j : Fin q,∃ v : Fin (∑ k,blockDimensions (coreA c) (freeW m c) k) → K,
          covector ell (mu (fun k => Q (j,k)) v) ≠ 0 := by
  apply principal_open_excludes_profile_of_int_bound mu
    (Cell m c i (levelCount r 1) (levelCount r 2) (levelCount r 3))
    (parameterCount_le_Cell m c i hi r hr)
  simpa only [sum_blockDimensions,sum_blockRanks i r hr] using hcount

end Quartic.IteratedCovectorCharts
