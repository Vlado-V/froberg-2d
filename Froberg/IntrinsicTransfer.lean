import Froberg.Transfer

/-! The transfer theorem directly in terms of the actual deleted target and
the actual coefficient kernel, without separately supplied dimension identities. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] [Infinite K]
variable {W U : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U]
variable {n d r : ℕ}

theorem intrinsic_transfer_bounds (hn : 0 < n) (hr : r ≤ (n+d-1).choose d)
    (pi : Forms K n (2*d) →ₗ[K] W) (hpi : Function.Surjective pi)
    (q p : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (coeff : ProjectedEndpointHomology pi q →ₗ[K] U)
    (hNormal : finrank K (projectedNormalMap pi q p).range=
      min (finrank K (ProjectedEndpointHomology pi q ⧸ coeff.ker))
        (finrank K (ProjectedEndpointCokernel pi q))) :
    (genericHomology K n d r : ℤ) ≤ max (finrank K coeff.ker : ℤ)
      ((finrank K pi.ker : ℤ)-euler n d r) ∧
    (genericCokernel K n d r : ℤ) ≤ max (finrank K pi.ker : ℤ)
      ((finrank K coeff.ker : ℤ)+euler n d r) := by
  have hH := coeff.ker.finrank_quotient_add_finrank
  have hT := pi.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hpi,finrank_top,finrank_forms K n (2*d) hn] at hT
  exact transfer_bounds_of_projected_normal hn hr pi q p hq
    (finrank K coeff.ker) (finrank K (ProjectedEndpointHomology pi q ⧸ coeff.ker))
    (finrank K (ProjectedEndpointCokernel pi q)) (finrank K pi.ker)
    (by omega) rfl hT hNormal

theorem transfer_bounds_le_of_intrinsic (hn : 0 < n) (hr : r ≤ (n+d-1).choose d)
    (pi : Forms K n (2*d) →ₗ[K] W) (hpi : Function.Surjective pi)
    (q p : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (coeff : ProjectedEndpointHomology pi q →ₗ[K] U)
    (hNormal : finrank K (projectedNormalMap pi q p).range=
      min (finrank K (ProjectedEndpointHomology pi q ⧸ coeff.ker))
        (finrank K (ProjectedEndpointCokernel pi q)))
    (B : ℕ) (hcoeff : finrank K coeff.ker ≤ B) (hdelete : finrank K pi.ker ≤ B) :
    (genericHomology K n d r : ℤ) ≤ max (B : ℤ) ((B : ℤ)-euler n d r) ∧
    (genericCokernel K n d r : ℤ) ≤ max (B : ℤ) ((B : ℤ)+euler n d r) := by
  have hb := intrinsic_transfer_bounds hn hr pi hpi q p hq coeff hNormal
  have hc : (finrank K coeff.ker : ℤ) ≤ B := by exact_mod_cast hcoeff
  have ht : (finrank K pi.ker : ℤ) ≤ B := by exact_mod_cast hdelete
  exact ⟨hb.1.trans (max_le_max hc (sub_le_sub_right ht _)),
    hb.2.trans (max_le_max ht (by omega))⟩

end Froberg
