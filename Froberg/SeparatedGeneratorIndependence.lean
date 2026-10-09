module

public import Froberg.DetectedSymmetricProducts

@[expose] public section

/-! Separation of the new symmetric square also supplies the relative
independence of the new generators required by the homology coefficient map. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K]
variable {V Z : Type*} [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]
variable {ι : Type*}

/-- A nonzero vector has nonzero formal square in every characteristic. -/
theorem symProd_self_ne_zero {x : V} (hx : x ≠ 0) : symProd (K := K) x x ≠ 0 := by
  have hi : LinearIndependent K (fun _ : Unit => x) := linearIndependent_unique_iff.mpr hx
  exact (linearIndependent_formalPair (fun _ : Unit => x) hi).ne_zero s((),())

/-- The new generator space is disjoint from the old generator space whenever
its formal symmetric square is separated from the old polynomial products. -/
theorem disjoint_generators_of_formalSquare_separated
    (μ : SymmetricSquare K V →ₗ[K] Z) (F W : Submodule K V)
    (hsep : formalSquare F ⊓ ((formalMixed W).map μ).comap μ = ⊥) :
    Disjoint F W := by
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hxF,hxW⟩
  change x = 0
  by_contra hx
  have hformal : symProd (K := K) x x ∈ formalSquare F :=
    ⟨symProd (K := K) (⟨x,hxF⟩ : F) ⟨x,hxF⟩, symmetricMap_symProd _ _ _⟩
  have hmixed : symProd (K := K) x x ∈
      ((formalMixed W).map μ).comap μ :=
    ⟨symProd (K := K) x x, symProd_mem_formalMixed W hxW x, rfl⟩
  have hz : symProd (K := K) x x ∈ (⊥ : Submodule K (SymmetricSquare K V)) :=
    hsep ▸ (show symProd (K := K) x x ∈
      formalSquare F ⊓ ((formalMixed W).map μ).comap μ from ⟨hformal,hmixed⟩)
  exact symProd_self_ne_zero hx hz

/-- Thus an independent new family remains independent modulo the old
space, without an extra genericity assumption. -/
theorem linearIndependent_quotient_of_formalSquare_separated
    (μ : SymmetricSquare K V →ₗ[K] Z) (W : Submodule K V)
    (f : ι → V) (hf : LinearIndependent K f)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map μ).comap μ = ⊥) :
    LinearIndependent K (fun i => W.mkQ (f i)) := by
  have hd := disjoint_generators_of_formalSquare_separated μ _ W hsep
  exact hf.map_injOn W.mkQ (LinearMap.disjoint_ker_iff_injOn.mp (by simpa using hd))

end Froberg
