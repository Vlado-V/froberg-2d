module

public import Froberg.ParameterPullbackOpen
public import Froberg.GenericDimensions
public import Quartic.PolynomialRankOpen

@[expose] public section

/-! Finitely many nonempty principal opens have a common actual vector. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K V I : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype I]

theorem finite_basis_principal_intersection
    (D : I → MvPolynomial (Fin (finrank K V)) K)
    (hD : ∀ i,∃ v : V,eval ((Module.finBasis K V).equivFun v) (D i)≠0) :
    ∃ v : V,∀ i,eval ((Module.finBasis K V).equivFun v) (D i)≠0 := by
  have hnz (i : I) : D i≠0 := by
    obtain ⟨v,hv⟩ := hD i
    intro hz
    exact hv (by rw [hz,map_zero])
  obtain ⟨x,hx⟩ := Quartic.nonempty_principal_intersection D hnz
  exact ⟨(Module.finBasis K V).equivFun.symm x,by simpa only [LinearEquiv.apply_symm_apply] using hx⟩

end Froberg
