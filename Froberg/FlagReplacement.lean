module

public import Froberg.CriticalChildFlag
public import Froberg.PreparedHyperplane
public import Froberg.FormalHyperplane

@[expose] public section

/-! Exact replacement for an embedded scalar flag and literal independent
positive columns. All subspace hypotheses of the hyperplane lemma are
proved from the column data. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} {U V I : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] {q : ℕ}

def embeddedFlagSpace (j : U →ₗ[K] V) (Q : Fin q → U) : Submodule K V :=
  (Submodule.span K (Set.range Q)).map j

def replacedFlagBackground (j : U →ₗ[K] V) (Q : Fin q → U) (hq : 0 < q)
    (b : I → V) (M : V) (ε : K) : Submodule K V :=
  (embeddedFlagSpace j (scalarFlagPrefix Q) ⊔ Submodule.span K (Set.range b)) ⊔
    Submodule.span K {j (Q (lastScalarSlot hq))+ε • M}

theorem embeddedFlagSpace_split (j : U →ₗ[K] V) (Q : Fin q → U) (hq : 0 < q) :
    embeddedFlagSpace j Q=embeddedFlagSpace j (scalarFlagPrefix Q) ⊔
      Submodule.span K {j (Q (lastScalarSlot hq))} := by
  unfold embeddedFlagSpace
  rw [scalarFlag_span hq Q,Submodule.map_sup]
  simp only [Submodule.map_span,Set.image_singleton]

theorem embeddedFlagSpace_last_not_mem (j : U →ₗ[K] V) (hj : Function.Injective j)
    (Q : Fin q → U) (hQ : LinearIndependent K Q) (hq : 0 < q) :
    j (Q (lastScalarSlot hq))∉embeddedFlagSpace j (scalarFlagPrefix Q) := by
  rintro ⟨x,hx,he⟩
  have hxQ := hj he
  exact scalarFlag_last_not_mem hq Q hQ (hxQ ▸ hx)

theorem flag_replacement_formal_relations
    (j : U →ₗ[K] V) (hj : Function.Injective j)
    (Q : Fin q → U) (hQ : LinearIndependent K Q) (hq : 0 < q)
    (b : I → V) (M : V)
    (hpositive : LinearIndependent K (fun i : Option I => j.range.mkQ (i.elim M b)))
    (R : Submodule K (SymmetricSquare K V))
    (hrelations : R ⊓ formalMixed ((embeddedFlagSpace j Q ⊔ Submodule.span K (Set.range b)) ⊔
        Submodule.span K {M})=R ⊓ formalProducts (embeddedFlagSpace j Q) j.range)
    (ε : K) (hε : ε≠0) :
    R ⊓ formalMixed (replacedFlagBackground j Q hq b M ε)=
      R ⊓ formalProducts (embeddedFlagSpace j (scalarFlagPrefix Q)) j.range := by
  have hB : Disjoint (Submodule.span K (Set.range b)) j.range := by
    apply span_disjoint_of_independent_quotient
    exact hpositive.comp (@Option.some I) (Option.some_injective I)
  have hM : M∉Submodule.span K (Set.range b) ⊔ j.range :=
    extra_not_mem_of_independent_quotient j.range b M hpositive
  have hdata := prepared_hyperplane_subspace_data j.range (embeddedFlagSpace j Q)
    (embeddedFlagSpace j (scalarFlagPrefix Q)) (Submodule.span K (Set.range b))
    (j (Q (lastScalarSlot hq))) M (LinearMap.map_le_range)
    (embeddedFlagSpace_split j Q hq) hB (embeddedFlagSpace_last_not_mem j hj Q hQ hq) hM
  exact formal_hyperplane_replacement R _ _ _ _ _ hdata.1 (embeddedFlagSpace_split j Q hq)
    hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2 hε hrelations

end Froberg
