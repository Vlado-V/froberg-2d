module

public import Froberg.LinearEndpoint
public import Froberg.RowTwoCounts

@[expose] public section

/-! A concrete linear output space and its exact quadratic quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K : Type*} [Field K]

theorem exists_linear_space_with_quadratic_quotient {h p : ℕ} (hh : 0 < h) (hp : p ≤ h) :
    ∃ A : Submodule K (Poly K h), A ≤ Forms K h 1 ∧ finrank K A=p ∧
      finrank K (EndpointQuotient K h 1 A)=(h-p+1).choose 2 := by
  have hdim : p ≤ finrank K (Forms K h 1) := by simpa [finrank_forms K h 1 hh] using hp
  obtain ⟨q,hq⟩ := exists_linearIndependent_of_le_finrank hdim
  let A := Submodule.span K (Set.range (fun i => (q i).val))
  have hA : A ≤ Forms K h 1 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (q i).property
  refine ⟨A,hA,?_,?_⟩
  · have hi := hq.map' (Forms K h 1).subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
    simpa only [A,Function.comp_def,Fintype.card_fin,Submodule.subtype_apply] using finrank_span_eq_card hi
  · have he := endpoint_quotient_linear hh q hq
    simpa only [A,expectedEndpoint,euler_linear hp,Int.toNat_natCast] using he

end Froberg
