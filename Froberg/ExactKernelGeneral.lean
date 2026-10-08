import Froberg.ExactKernelOpen

/-! Finite-domain rank openness does not require a finite-dimensional target.
This permits row maps into the actual polynomial ring. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K ι U V W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

theorem rank_polynomial_general_open
    (A : (ι → K) → (V →ₗ[K] W)) (hA : IsPolynomialFamily A) (a₀ : ι → K) :
    ∃ D : MvPolynomial ι K,eval a₀ D≠0 ∧ ∀ a,eval a D≠0 →
      finrank K (A a₀).range≤finrank K (A a).range := by
  classical
  let R := (A a₀).range
  let b := Module.finBasis K R
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map' R.subtype (LinearMap.ker_eq_bot.mpr R.injective_subtype)
  have hpre : ∀ i,∃ x,A a₀ x=(b i).val := fun i => (b i).property
  choose x hx using hpre
  let q : Fin (finrank K R) → (ι → K) → W := fun i a => A a (x i)
  have hqpoly (i) : IsPolynomialFamily (q i) :=
    hA.linear_comp (LinearMap.applyₗ (R := K) (M₂ := W) (x i))
  have hq : LinearIndependent K (fun i => q i a₀) := by simpa only [q,hx] using hb
  obtain ⟨D,hD,hfamily⟩ := independent_polynomial_principal_open q hqpoly a₀ hq
  refine ⟨D,hD,?_⟩
  intro a ha
  have hle : Submodule.span K (Set.range (fun i => q i a))≤(A a).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨x i,rfl⟩
  have h := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card (hfamily a ha),Fintype.card_fin] at h

/-- Literal kernel equality persists in the polynomial ring when its source
and its mandatory relation parameter space are finite-dimensional. -/
theorem exact_kernel_general_open
    (A : (ι → K) → (V →ₗ[K] W)) (Z : (ι → K) → (U →ₗ[K] V))
    (hA : IsPolynomialFamily A) (hZ : IsPolynomialFamily Z)
    (hAZ : ∀ a,(A a).comp (Z a)=0)
    (a₀ : ι → K) (hZ₀ : Function.Injective (Z a₀))
    (hexact : (A a₀).ker=(Z a₀).range) :
    ∃ D : MvPolynomial ι K,eval a₀ D≠0 ∧
      ∀ a,eval a D≠0 → Function.Injective (Z a) ∧ (A a).ker=(Z a).range := by
  obtain ⟨DA,hDA,hArank⟩ := rank_polynomial_general_open A hA a₀
  obtain ⟨DZ,hDZ,hZinj⟩ := injective_polynomial_principal_open Z hZ a₀ hZ₀
  refine ⟨DA*DZ,by simpa only [map_mul] using mul_ne_zero hDA hDZ,?_⟩
  intro a ha
  rw [map_mul] at ha
  have hinj := hZinj a (mul_ne_zero_iff.mp ha).2
  refine ⟨hinj,?_⟩
  have hle : (Z a).range≤(A a).ker := by
    rintro x ⟨u,rfl⟩
    exact LinearMap.congr_fun (hAZ a) u
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  have hdim₀ := LinearMap.finrank_range_add_finrank_ker (A a₀)
  rw [hexact,LinearMap.finrank_range_of_inj hZ₀] at hdim₀
  have hdim := LinearMap.finrank_range_add_finrank_ker (A a)
  have hbig := hArank a (mul_ne_zero_iff.mp ha).1
  rw [LinearMap.finrank_range_of_inj hinj]
  omega

end Froberg
