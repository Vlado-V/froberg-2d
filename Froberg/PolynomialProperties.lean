module

public import Quartic.PolynomialRankOpen

@[expose] public section

/-! Explicit certificates for finite intersections of polynomial conditions. -/
noncomputable section
namespace Froberg
open MvPolynomial Quartic
variable {K I J : Type*} [Field K] [Infinite K] [Fintype J]

theorem principal_property_common_open (P : J → (I → K) → Prop)
    (hP : ∀ j, ∃ D : MvPolynomial I K, (∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → P j a) :
    ∃ D : MvPolynomial I K, (∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → ∀ j,P j a := by
  classical
  choose D hD hprop using hP
  have hne (j : J) : D j≠0 := by
    obtain ⟨a,ha⟩ := hD j
    intro hz
    exact ha (by rw [hz,map_zero])
  obtain ⟨a,ha⟩ := nonempty_principal_intersection D hne
  refine ⟨∏ j,D j,⟨a,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun j _ => ha j)
  intro a ha j
  have he : ∏ j,eval a (D j)≠0 := by simpa only [map_prod] using ha
  exact hprop j a (Finset.prod_ne_zero_iff.mp he j (Finset.mem_univ _))

end Froberg
