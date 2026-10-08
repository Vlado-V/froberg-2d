import Froberg.ActualThinProjectedNormal
import Froberg.RetainedTransfer

/-! The actual retained child homology and deleted child cokernel give
the two critical-defect bounds in the final local comparison. -/
noncomputable section
namespace Froberg
open Module Quartic BilinearScalarFamily
attribute [local irreducible] upperCount
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {F V W : Type*}
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {m n d r t c : ℕ}

theorem exists_local_comparison_from_retained (htwo : (2 : K)≠0) (hm : 0 < m)
    (D : Submodule K (Forms K n (2*d))) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] V)
    (eJ : ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] W)
    (phi : F →ₗ[K] Forms K n d) (mu : F →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ z v,mu z (vmap v)=eJ (projectedQuotientProduct D.mkQ q (phi z) v))
    (C : ℝ) (hC : (t : ℝ)≤C)
    (hslices : HasClosedKernelSlices mu (BilinearCovectorStrata.thinSlices (finrank K W) C))
    (T : Submodule K (Forms K n d)) (hT : T≤Submodule.span K (Set.range q))
    (old : Fin c → Forms K m d) (hold : LinearIndependent K old)
    (hc : c=upperCount m d-1)
    (hgeneric : finrank K (EndpointHomology old)=genericHomology K m d c)
    (f : Fin m ↪ Fin n)
    (hinj : Set.InjOn (D.mkQ.comp (renameForm f)) (endpointMultiplication old).range)
    (hrel : (D.mkQ.comp formalPolynomialMultiplication).ker ⊓ formalMixed T=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range old)).map (renameForm f)) (renameForm f).range)
    (hcoeff : (actualProjectedMappedCoefficients htwo D.mkQ q hq dual vmap).ker=
      projectedRetainedHomology htwo D.mkQ q hq T)
    (hdeleted : finrank K D=genericCokernel K m d (upperCount m d)) :
    Nonempty (LocalComparisonData K n d r (criticalDefect K m d)) := by
  apply exists_local_comparison_of_actual_thin_slices htwo D q hq dual vmap eJ phi mu hmu C hC hslices
  · exact coefficient_kernel_critical_bound htwo hm D.mkQ q hq T hT old hold hc hgeneric f hinj hrel
      (actualProjectedMappedCoefficients htwo D.mkQ q hq dual vmap) hcoeff
  · rw [hdeleted]
    exact (critical_child_defects_le htwo hm).2

end Froberg
