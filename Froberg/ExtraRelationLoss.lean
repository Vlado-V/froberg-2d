import Froberg.TensorFormCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The exact loss from imposing the remaining mixed-pure equations.
No extension or consistency assumption is made for these equations. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module TensorProduct
attribute [local instance] tensorFormGroup
variable {K E V : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem quotient_extra_relation_loss (A : Submodule K V) (g : E →ₗ[K] V) :
    finrank K (V ⧸ A)≤finrank K (V ⧸ (A ⊔ g.range))+finrank K E := by
  have hA := A.finrank_quotient_add_finrank
  have hB := (A ⊔ g.range).finrank_quotient_add_finrank
  have hsup := A.finrank_sup_add_finrank_inf_eq g.range
  have hr := g.finrank_range_le
  omega

theorem annihilator_extra_relation_loss (A : Submodule K V) (g : E →ₗ[K] V) :
    finrank K A.dualAnnihilator≤finrank K (A ⊔ g.range).dualAnnihilator+finrank K E := by
  have hA := Subspace.finrank_add_finrank_dualAnnihilator_eq A
  have hB := Subspace.finrank_add_finrank_dualAnnihilator_eq (A ⊔ g.range)
  have hsup := A.finrank_sup_add_finrank_inf_eq g.range
  have hr := g.finrank_range_le
  omega

theorem biform_extra_relation_loss {I : Type*} [Fintype I]
    {h m u : ℕ} (hh : 0 < h) (hm : 0 < m) (x y : I → ℕ)
    (A : Submodule K V)
    (g : (Fin u → (i : I) → Forms K h (x i) ⊗[K] Forms K m (y i)) →ₗ[K] V) :
    finrank K A.dualAnnihilator≤finrank K (A ⊔ g.range).dualAnnihilator+
      u*∑ i,(h+x i-1).choose (x i)*(m+y i-1).choose (y i) := by
  have hd : finrank K (Fin u → (i : I) → Forms K h (x i) ⊗[K] Forms K m (y i))=
      u*∑ i,(h+x i-1).choose (x i)*(m+y i-1).choose (y i) := by
    simp [Module.finrank_pi_fintype,Module.finrank_tensorProduct,finrank_forms K h _ hh,
      finrank_forms K m _ hm]
  have hbound := annihilator_extra_relation_loss (K := K)
    (E := Fin u → (i : I) → Forms K h (x i) ⊗[K] Forms K m (y i)) (V := V) A g
  rw [hd] at hbound
  exact hbound

end Froberg
