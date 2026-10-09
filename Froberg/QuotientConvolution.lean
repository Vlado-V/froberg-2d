module

public import Froberg.OutputSpaceExtension

@[expose] public section

/-! Convolution in a quotient output space, lifted into a prescribed
larger subspace of the actual output space. -/
noncomputable section
namespace Froberg
open Module
variable {K V Q : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup Q] [Module K Q] [Module.Finite K Q]

/-- A surjective linear quotient admits a surjective restriction of every
permitted dimension at least the quotient dimension. -/
theorem exists_surjective_restriction (π : V →ₗ[K] Q) (hπ : Function.Surjective π)
    {D : ℕ} (hlo : finrank K Q ≤ D) (hhi : D ≤ finrank K V) :
    ∃ W : Submodule K V, finrank K W = D ∧ Function.Surjective (π.comp W.subtype) := by
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hsinj : Function.Injective s := by
    intro a b hab
    have hab' := congrArg π hab
    simpa only [← LinearMap.comp_apply,hs,LinearMap.id_apply] using hab'
  have hdim : finrank K s.range ≤ D := by rw [LinearMap.finrank_range_of_inj hsinj]; exact hlo
  obtain ⟨W,hW,hWD⟩ := Quartic.SplitMiddle22.exists_extension_finrank s.range D hdim hhi
  refine ⟨W,hWD,fun q => ⟨⟨s q,hW ⟨q,rfl⟩⟩,?_⟩⟩
  exact LinearMap.congr_fun hs q

/-- The lifted forms fill the quotient while every actual output coefficient
belongs to one fixed output subspace of the requested dimension. -/
theorem exists_lifted_convolution_family [Infinite K]
    (π : V →ₗ[K] Q) (hπ : Function.Surjective π)
    {D a e m r : ℕ} (hlo : finrank K Q ≤ D) (hhi : D ≤ finrank K V)
    (ha : 0 < a) (hm : 0 < m)
    (hr : convolutionBlockCount (finrank K Q) a e*(m+a+e-2).choose e ≤ r) :
    ∃ (W : Submodule K V) (o : Fin r → W) (f : Fin r → Forms K m e),
      finrank K W = D ∧
      Function.Surjective (vectorFormFamilyMap (t := a-1) (fun i => π (o i).val) f) := by
  obtain ⟨W,hWD,hWπ⟩ := exists_surjective_restriction π hπ hlo hhi
  obtain ⟨o,f,hs⟩ := exists_convolution_family_of_count (K := K) (W := Q) ha hm hr
  choose O hO using fun i => hWπ (o i)
  refine ⟨W,O,f,hWD,?_⟩
  have heq : (fun i => π (O i).val) = o := funext hO
  rwa [heq]

end Froberg
