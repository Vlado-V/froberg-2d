import Quartic.UniformSurplus.Counts

/-! Agreement with the rational sharp expression used by the finite exact
certificates. This fixes the meaning of the real polynomial extension. -/
namespace Quartic.UniformSurplus
noncomputable section

theorem H₂Real_cast (w : ℤ) (n : ℚ) :
    H₂Real (w:ℝ) (n:ℝ)=(SharpCertificate.H₂ w n:ℝ) := by
  unfold H₂Real quadraticReal SharpCertificate.H₂
  push_cast
  ring

theorem H₃Real_cast (w : ℤ) (n : ℚ) :
    H₃Real (w:ℝ) (n:ℝ)=(SharpCertificate.H₃ w n:ℝ) := by
  unfold H₃Real cubicReal SharpCertificate.H₃
  push_cast
  ring

/-- Exact identification with `SharpCertificate.sharpProfile`, already used
by the finite source-linked certificate modules. -/
theorem sourceSharp_eq_rational (m c i : ℕ) (n₁ n₂ n₃ : ℚ) :
    sourceSharp m c i n₁ n₂ n₃=
      (SharpCertificate.sharpProfile (SharpCertificate.parameters m c i) n₁ n₂ n₃:ℝ) := by
  have hhalf : (ProfileCertificate.coreA c:ℝ)/2=(ProfileCertificate.coreP c:ℝ) := by
    simp only [ProfileCertificate.coreA, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hq : (FiniteCounts.quadratics (ProfileCertificate.freeW m c):ℝ)=
      quadraticReal (ProfileCertificate.freeW m c) := by
    simp only [FiniteCounts.quadratics_eq_b2, UniformScalar.b2_cast, quadraticReal]
  unfold sourceSharp sharpReal SharpCertificate.sharpProfile SharpCertificate.parameters
  push_cast
  rw [hhalf,hq]
  have h₂₁ := H₂Real_cast (ProfileCertificate.freeW m c) n₁
  have h₂₂ := H₂Real_cast (ProfileCertificate.freeW m c) n₂
  have h₃₁ := H₃Real_cast (ProfileCertificate.freeW m c) n₁
  have h₃₂ := H₃Real_cast (ProfileCertificate.freeW m c) n₂
  have h₃₃ := H₃Real_cast (ProfileCertificate.freeW m c) n₃
  norm_cast at h₂₁ h₂₂ h₃₁ h₃₂ h₃₃
  rw [h₂₁,h₂₂,h₃₁,h₃₂,h₃₃]

end
end Quartic.UniformSurplus
