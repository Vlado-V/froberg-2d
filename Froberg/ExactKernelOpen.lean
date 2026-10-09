module

public import Quartic.PolynomialRankOpen

@[expose] public section

/-! Exactness with a fixed-dimensional mandatory kernel is a polynomial open
condition. This applies directly to the row-wise constant Koszul kernels. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K ι U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- One exact polynomial row gives a principal open of exact rows, including
injectivity of the mandatory-kernel parameterization. -/
theorem exact_kernel_principal_open
    (A : (ι → K) → (V →ₗ[K] W)) (Z : (ι → K) → (U →ₗ[K] V))
    (hA : IsPolynomialFamily A) (hZ : IsPolynomialFamily Z)
    (hAZ : ∀ a,(A a).comp (Z a)=0)
    (a₀ : ι → K) (hZ₀ : Function.Injective (Z a₀))
    (hexact : (A a₀).ker=(Z a₀).range) :
    ∃ D : MvPolynomial ι K,eval a₀ D≠0 ∧
      ∀ a,eval a D≠0 → Function.Injective (Z a) ∧ (A a).ker=(Z a).range := by
  obtain ⟨DA,hDA,hArank⟩ := rank_polynomial_principal_open A hA a₀
  obtain ⟨DZ,hDZ,hZinj⟩ := injective_polynomial_principal_open Z hZ a₀ hZ₀
  refine ⟨DA*DZ,by simpa only [map_mul] using mul_ne_zero hDA hDZ,?_⟩
  intro a ha
  rw [map_mul] at ha
  have haA := (mul_ne_zero_iff.mp ha).1
  have haZ := (mul_ne_zero_iff.mp ha).2
  have hinj := hZinj a haZ
  refine ⟨hinj,?_⟩
  have hle : (Z a).range≤(A a).ker := by
    rintro x ⟨u,rfl⟩
    exact LinearMap.congr_fun (hAZ a) u
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hdim₀ := LinearMap.finrank_range_add_finrank_ker (A a₀)
  rw [hexact,LinearMap.finrank_range_of_inj hZ₀] at hdim₀
  have hdim := LinearMap.finrank_range_add_finrank_ker (A a)
  have hbig := hArank a haA
  rw [LinearMap.finrank_range_of_inj hinj]
  omega

end Froberg
