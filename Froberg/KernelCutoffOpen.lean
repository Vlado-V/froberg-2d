import Froberg.PolynomialKernelFrame
import Froberg.SurjectiveParameterOpen
import Quartic.BilinearImage

/-! Surjectivity of multiplication by the kernel of a varying projection
is an open condition at a surjective projection. The proof constructs
polynomial kernel vectors in the ambient space. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic
variable {K I E W T : Type*} [Field K] [Infinite K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup T] [Module K T] [FiniteDimensional K T] {b : ℕ}

theorem kernel_bilinear_surjective_open
    (P : (I → K) → W →ₗ[K] (Fin b → K)) (hP : IsPolynomialFamily P)
    (p₀ : I → K) (hP₀ : Function.Surjective (P p₀))
    (nu : E →ₗ[K] W →ₗ[K] T)
    (hcut : BilinearImage.image nu (P p₀).ker=⊤) :
    ∃ D : MvPolynomial I K,eval p₀ D≠0 ∧
      ∀ p,eval p D≠0 → BilinearImage.image nu (P p).ker=⊤ := by
  obtain ⟨S,hS⟩ := (P p₀).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hP₀)
  obtain ⟨F,hF,hPF,hF₀⟩ := exists_polynomial_kernel_frame P hP p₀ S hS (P p₀).ker le_rfl
  let basis := Module.finBasis K (P p₀).ker
  let q (p : I → K) := fun i => F p (basis i)
  have hspan : Submodule.span K (Set.range (q p₀))=(P p₀).ker := by
    change Submodule.span K (Set.range (F p₀ ∘ basis))=_
    rw [Set.range_comp,← Submodule.map_span,basis.span_eq,Submodule.map_top,hF₀]
    exact Submodule.range_subtype _
  let A (p : I → K) := BilinearImage.tupleMap nu (q p)
  have hA : IsPolynomialFamily A := by
    apply isPolynomialFamily_linearMap
    intro x
    have hh := IsPolynomialFamily.sum (fun i =>
      (hF.linear_comp (LinearMap.applyₗ (R := K) (M₂ := W) (basis i))).linear_comp (nu (x i)))
    change IsPolynomialFamily (fun p => ∑ i,nu (x i) (F p (basis i))) at hh
    simpa only [A,q,BilinearImage.tupleMap_apply] using hh
  have hA₀ : Function.Surjective (A p₀) := by
    apply LinearMap.range_eq_top.mp
    rw [BilinearImage.range_tupleMap,hspan,hcut]
  obtain ⟨D,hD,hgood⟩ := surjective_polynomial_principal_open A hA p₀ hA₀
  refine ⟨D,hD,fun p hp => ?_⟩
  have hinc : Submodule.span K (Set.range (q p))≤(P p).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact LinearMap.congr_fun (hPF p) (basis i)
  apply top_unique
  have htop : BilinearImage.image nu (Submodule.span K (Set.range (q p)))=⊤ := by
    rw [← BilinearImage.range_tupleMap]
    exact LinearMap.range_eq_top.mpr (hgood p hp)
  rw [← htop]
  exact iSup_mono (fun e => Submodule.map_mono hinc)

end Froberg
