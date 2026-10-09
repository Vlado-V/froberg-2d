module

public import Froberg.HomogeneousRename

@[expose] public section

/-! Deleting precisely a complement of an embedded old multiplication
image preserves that image and fills the embedded old target. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module
variable {K : Type} {V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_supported_target_deletion (j : V →ₗ[K] W) (hj : Function.Injective j)
    (U : Submodule K V) :
    ∃ Z : Submodule K W,
      finrank K Z=finrank K (V ⧸ U) ∧
      Z≤j.range ∧
      Set.InjOn Z.mkQ (U.map j) ∧
      (LinearMap.range j).map Z.mkQ=(U.map j).map Z.mkQ := by
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl U
  let Z := C.map j
  have hdim : finrank K Z=finrank K (V ⧸ U) := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hC
    have hquot := U.finrank_quotient_add_finrank
    have hmap : finrank K Z=finrank K C := (Submodule.equivMapOfInjective j hj C).finrank_eq.symm
    omega
  have hdis : Disjoint (U.map j) Z := Submodule.disjoint_map hj hC.disjoint
  have hi : Set.InjOn Z.mkQ (U.map j) := by
    rw [← LinearMap.disjoint_ker_iff_injOn]
    simpa only [Submodule.ker_mkQ] using hdis
  have hjrange : U.map j ⊔ Z=LinearMap.range j := by
    rw [← Submodule.map_sup,hC.sup_eq_top,Submodule.map_top]
  refine ⟨Z,hdim,LinearMap.map_le_range,hi,?_⟩
  rw [← hjrange,Submodule.map_sup]
  simp

variable {n m d r : ℕ}

theorem exists_supported_old_target_deletion (f : Fin m ↪ Fin n) (q : Fin r → Forms K m d) :
    ∃ D : Submodule K (Forms K n (2*d)),
      finrank K D=finrank K (EndpointQuotient K m d
        (Submodule.span K (Set.range (fun i => (q i).val)))) ∧
      D≤(renameForm (K := K) (d := 2*d) f).range ∧
      Set.InjOn (D.mkQ.comp (renameForm f)) (endpointMultiplication q).range ∧
      (renameForm (K := K) (d := 2*d) f).range.map D.mkQ=
        ((endpointMultiplication q).range.map (renameForm f)).map D.mkQ := by
  obtain ⟨D,hD,hsupport,hinj,hfill⟩ := exists_supported_target_deletion
    (renameForm (K := K) (d := 2*d) f) (renameForm_injective f) (endpointMultiplication q).range
  refine ⟨D,?_,hsupport,?_,hfill⟩
  · rwa [range_endpointMultiplication] at hD
  · intro a ha b hb hab
    apply renameForm_injective f
    exact hinj ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ hab

end Froberg
