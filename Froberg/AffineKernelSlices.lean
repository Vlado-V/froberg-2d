import Froberg.AffineKernelProfiles
import Froberg.AffineKernelBudget

/-! The actual kernel slice is empty after adjoining the independently
proved bottom-zero exclusion. -/
noncomputable section
namespace Froberg
open Module Quartic Quartic.BilinearCovectorCharts Quartic.BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {a b T T₀ q s threshold : ℕ}

theorem kernel_slice_empty
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (bottom : (Fin T → K) →ₗ[K] (Fin T₀ → K))
    (Q : Fin q → Fin b → K) (Z : Fin s → Fin T → K)
    (havoid : ∀ ell : Fin T → K,bottom ell≠0 →
      threshold≤finrank K (relationMap mu ell).ker → KernelCovectorExcluded mu B (Q,Z) ell)
    (hbottom : ∀ ell : Fin T → K,bottom ell=0 →
      (∀ i v,covector ell (mu (Q i) v+B i v)=0) → ell=0) :
    ∀ ell : Fin T → K,(∀ i v,covector ell (mu (Q i) v+B i v)=0) →
      threshold≤finrank K (relationMap mu ell).ker →
      (∀ j,covector ell (Z j)=0) → ell=0 := by
  intro ell hproducts hk hcuts
  by_cases hb : bottom ell=0
  · exact hbottom ell hb hproducts
  · exact (havoid ell hb hk ⟨hproducts,hcuts⟩).elim

end Froberg
