import Froberg.AffineKernelCharts

/-! The first-stage chart equations vanish on the actual relation kernel. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.BilinearCovectorCharts
open Quartic.BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K]
variable {a b T T₀ H k : ℕ}

theorem affineKernelChart_zero
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (bottom : (Fin T → K) →ₗ[K] (Fin T₀ → K))
    (higher : (Fin T → K) →ₗ[K] (Fin H → K))
    (hcompat : ∀ ell p v,covector ell (mu p v)=
      covector (bottom ell) (mu₀ p v)+covector (higher ell) (muH p v))
    (ell : Fin T → K) (j : Fin k ↪ Fin a) (u : Fin (graphParameterCount j) → K)
    (hspan : Submodule.span K (Set.range (graphFromFin j u))≤(relationMap mu ell).ker) :
    affineKernelChart mu₀ muH j (Fin.append (bottom ell) u) (higher ell,1)=0 := by
  unfold affineKernelChart
  rw [chartBottom_append (K := K),chartGraphCoordinates_append (K := K)]
  ext l
  have hv : graphFromFin j u (finProdFinEquiv.symm l).1 ∈ (relationMap mu ell).ker :=
    hspan (Submodule.subset_span (Set.mem_range_self _))
  have he := congrFun (LinearMap.mem_ker.mp hv) (finProdFinEquiv.symm l).2
  simp only [relationMap_apply,Pi.zero_apply,hcompat] at he
  simp only [affineGraphConstraint,affineHomogenization_apply,one_smul,Pi.add_apply,
    tupleProductConstraint_apply]
  exact (add_comm _ _).trans he

end Froberg
