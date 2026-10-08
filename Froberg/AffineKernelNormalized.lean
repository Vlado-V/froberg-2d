import Froberg.AffineKernelChartZero
import Froberg.AffineLayeredAvoidance

/-! One normalized bottom slice and one actual kernel chart. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.BilinearCovectorCharts
open Quartic.BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {a b T T₀ H k q s s₀ nf r : ℕ}

def KernelCovectorExcluded
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (y : SharedCovectorPolynomial.Input K b T q s) (ell : Fin T → K) : Prop :=
  ¬ ((∀ i v,covector ell (mu (y.1 i) v+B i v)=0) ∧
    (∀ j,covector ell (y.2 j)=0))

theorem affine_kernel_normalized_joint
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (bottom : (Fin T → K) →ₗ[K] (Fin T₀ → K))
    (higher : (Fin T → K) →ₗ[K] (Fin H → K))
    (res : ((Fin T₀ → K) × (Fin H → K)) →ₗ[K] (Fin T → K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,covector ell (mu p v)=
      covector (bottom ell) (mu₀ p v)+covector (higher ell) (muH p v))
    (degrees : Fin nf → ℕ) (f : ∀ i,Forms K T₀ (degrees i))
    (cuts : Fin (s₀+1) → Forms K T₀ 1)
    (hempty : ∀ t : Fin T₀ → K,(∀ i,eval t (f i).val=0) →
      (∀ i,eval t (cuts i).val=0) → t=0)
    (j : Fin k ↪ Fin a)
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (hcount : s₀+a*k+(H+1)<r+q*(a-k)+s) :
    ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 →
      ∀ ell : Fin T → K,ell≠0 →
        (∀ i,eval (bottom ell) (f i).val=0) → eval (bottom ell) (cuts 0).val=1 →
        ∀ u : Fin (graphParameterCount j) → K,
        Submodule.span K (Set.range (graphFromFin j u))=(relationMap mu ell).ker →
        r≤finrank K (BilinearImage.image muH (relationMap mu ell).ker) →
        KernelCovectorExcluded mu B y ell := by
  have hdim : finrank K ((Fin H → K) × K)=H+1 := by
    simp only [Module.finrank_prod,Module.finrank_pi,Module.finrank_self,Fintype.card_fin,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  have hc : s₀+graphParameterCount j+finrank K ((Fin H → K) × K)<r+q*(a-k)+s := by
    rw [hdim]
    have := graphParameterCount_bound j
    omega
  obtain ⟨D,hD,hgood⟩ := affine_layered_covectors_joint degrees f cuts hempty
    (affineKernelChart mu₀ muH j) (chartCovector res j)
    (affineKernelChart_polynomial mu₀ muH j) (chartCovector_polynomial res j) mu B hc
  refine ⟨D,hD,?_⟩
  intro y hy ell hne hf hslice u hspan hr
  have hlambda : chartCovector res j (Fin.append (bottom ell) u) (higher ell,1)=ell := by
    dsimp only [chartCovector]
    rw [chartBottom_append (K := K),one_smul,hres]
  have hzero := affineKernelChart_zero mu mu₀ muH bottom higher hcompat ell j u hspan.le
  have hrank := affineKernelChart_rank mu₀ muH j (bottom ell) u
  rw [hspan] at hrank
  have hk : finrank K (relationMap mu ell).ker≤k := by
    rw [←hspan,graphFromFin,Quartic.BilinearCovectorCharts.graphVector_span,
      Quartic.SubspaceCharts.chartSubspace_finrank]
  have hg := hgood y hy (higher ell,1) (bottom ell) hf hslice u (hr.trans hrank)
  rw [hlambda] at hg
  exact hg hne hk hzero

end Froberg
