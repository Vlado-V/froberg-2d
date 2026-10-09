module

public import Froberg.FlagReplacement

@[expose] public section

/-! The replacement background is contained in the temporary background
with its extra column. Hence the C.2 separation for the temporary family
descends to every replacement parameter. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} {U V W I : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {q : ℕ}

theorem replacedFlagBackground_le
    (j : U →ₗ[K] V) (Q : Fin q → U) (hq : 0 < q)
    (b : I → V) (M : V) (ε : K) :
    replacedFlagBackground j Q hq b M ε≤
      (embeddedFlagSpace j Q ⊔ Submodule.span K (Set.range b)) ⊔ Submodule.span K {M} := by
  have hp : embeddedFlagSpace j (scalarFlagPrefix Q)≤embeddedFlagSpace j Q := by
    rw [embeddedFlagSpace_split j Q hq]
    exact le_sup_left
  apply sup_le
  · exact sup_le (hp.trans (le_sup_left.trans le_sup_left)) (le_sup_right.trans le_sup_left)
  · apply Submodule.span_le.mpr
    rintro x (rfl : x=j (Q (lastScalarSlot hq))+ε • M)
    apply Submodule.add_mem
    · apply (show embeddedFlagSpace j Q≤
          (embeddedFlagSpace j Q ⊔ Submodule.span K (Set.range b)) ⊔ Submodule.span K {M}
          from le_sup_left.trans le_sup_left)
      exact ⟨Q (lastScalarSlot hq),Submodule.subset_span ⟨_,rfl⟩,rfl⟩
    · apply Submodule.smul_mem
      exact (show Submodule.span K {M} ≤
        (embeddedFlagSpace j Q ⊔ Submodule.span K (Set.range b)) ⊔ Submodule.span K {M}
        from le_sup_right) (Submodule.subset_span (Set.mem_singleton M))

theorem formal_square_separation_mono
    (L : SymmetricSquare K V →ₗ[K] W) (A T T' : Submodule K V)
    (hT : T≤T')
    (hsep : formalSquare A ⊓ ((formalMixed T').map L).comap L=⊥) :
    formalSquare A ⊓ ((formalMixed T).map L).comap L=⊥ := by
  apply le_antisymm _ bot_le
  rw [←hsep]
  exact inf_le_inf le_rfl (Submodule.comap_mono (Submodule.map_mono (formalMixed_mono hT)))

theorem flag_replacement_separation
    (j : U →ₗ[K] V) (Q : Fin q → U) (hq : 0 < q)
    (b : I → V) (M : V) (ε : K)
    (L : SymmetricSquare K V →ₗ[K] W) (A : Submodule K V)
    (hsep : formalSquare A ⊓
      ((formalMixed ((embeddedFlagSpace j Q ⊔ Submodule.span K (Set.range b)) ⊔
        Submodule.span K {M})).map L).comap L=⊥) :
    formalSquare A ⊓ ((formalMixed (replacedFlagBackground j Q hq b M ε)).map L).comap L=⊥ :=
  formal_square_separation_mono L A _ _ (replacedFlagBackground_le j Q hq b M ε) hsep

end Froberg
