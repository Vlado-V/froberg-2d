import Froberg.ThinProjectedNormal
import Froberg.ActualClosedKernelSlices

/-! C.6 in the actual coefficient and target spaces. Coordinates preserve
the coefficient kernel and transport the closed-kernel slices, so the
normal-rank engine returns the required local comparison data directly. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Quartic PolynomialBilinearCoordinates BilinearScalarFamily
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {F V W Z : Type*}
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
variable {n d r t B : ℕ}

def actualProjectedMappedCoefficients (htwo : (2 : K)≠0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] V) :
    ProjectedEndpointHomology pi q →ₗ[K] (Fin t → V) :=
  (vmap.compLeft (Fin t)).comp
    (projectedHomologyCoefficients htwo pi q hq (Submodule.span K (Set.range q)) dual)

theorem projectedMappedCoefficients_coordinate_ker (htwo : (2 : K)≠0)
    (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] V) :
    (projectedMappedCoefficients htwo pi q hq dual
      ((coordinates K V).toLinearMap.comp vmap)).ker=
        (actualProjectedMappedCoefficients htwo pi q hq dual vmap).ker := by
  have he : projectedMappedCoefficients htwo pi q hq dual
      ((coordinates K V).toLinearMap.comp vmap)=
      ((coordinates K V).toLinearMap.compLeft (Fin t)).comp
        (actualProjectedMappedCoefficients htwo pi q hq dual vmap) := rfl
  rw [he]
  apply LinearMap.ker_comp_of_ker_eq_bot
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  funext i
  apply (coordinates K V).injective
  exact congrFun hxy i

theorem exists_local_comparison_of_actual_thin_slices (htwo : (2 : K)≠0)
    (D : Submodule K (Forms K n (2*d))) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) (dual : Fin t → Forms K n d →ₗ[K] K)
    (vmap : (Forms K n d ⧸ Submodule.span K (Set.range q)) →ₗ[K] V)
    (eJ : ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] W)
    (phi : F →ₗ[K] Forms K n d) (mu : F →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ z v,mu z (vmap v)=eJ (projectedQuotientProduct D.mkQ q (phi z) v))
    (C : ℝ) (hC : (t : ℝ)≤C)
    (hslices : HasClosedKernelSlices mu (BilinearCovectorStrata.thinSlices (finrank K W) C))
    (hkernel : finrank K (actualProjectedMappedCoefficients htwo D.mkQ q hq dual vmap).ker≤B)
    (hdeleted : finrank K D≤B) :
    Nonempty (LocalComparisonData K n d r B) := by
  obtain ⟨count,degrees,eqs,cuts,hiff,hempty⟩ := hslices
  apply exists_local_comparison_of_thin_slices htwo D q hq dual
    ((coordinates K V).toLinearMap.comp vmap)
    (eJ.trans (coordinates K W))
    (phi.comp (coordinates K F).symm.toLinearMap)
    (coordinateTensor mu) _ C hC count degrees eqs cuts hempty _ B _ hdeleted
  · intro z v
    simp only [coordinateTensor,transportBilinear_apply,LinearMap.comp_apply,
      LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,LinearEquiv.trans_apply]
    rw [hmu]
  · intro ell k hk
    exact (hiff k ell).mpr hk.ge
  · rwa [projectedMappedCoefficients_coordinate_ker]

end Froberg
