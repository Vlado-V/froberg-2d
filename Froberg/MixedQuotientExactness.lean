module

public import Froberg.Graded
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-! The exact mixed-row quotient sequence after an independent projected
family is adjoined. All terms are actual subspace quotients. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A new family disjoint from the old two-factor relations cannot create
an extra intersection with the first-factor relation space. -/
theorem mixed_intersection_of_disjoint (A B E : Submodule K V)
    (hE : Disjoint E (A ⊔ B)) : A ⊓ (B ⊔ E)=A ⊓ B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b,hb,e,he,hbe⟩ := Submodule.mem_sup.mp hx.2
    have heAB : e ∈ A ⊔ B := by
      have heq : e=x-b := by rw [← hbe]; abel
      rw [heq]
      exact Submodule.sub_mem _ ((show A ≤ A ⊔ B from le_sup_left) hx.1) ((show B ≤ A ⊔ B from le_sup_right) hb)
    have he0 : e=0 := (Submodule.mem_bot K).mp (disjoint_iff_inf_le.mp hE ⟨he,heAB⟩)
    have hbx : b=x := by simpa only [he0,add_zero] using hbe
    exact ⟨hx.1,hbx ▸ hb⟩
  · exact inf_le_inf_left A le_sup_left

def mixedRelationMap (A B E : Submodule K V) : A →ₗ[K] V ⧸ (B ⊔ E) :=
  (B ⊔ E).mkQ.comp A.subtype

theorem mixedRelationMap_kernel (A B E : Submodule K V)
    (hE : Disjoint E (A ⊔ B)) : (mixedRelationMap A B E).ker=B.comap A.subtype := by
  ext x
  change x.val ∈ (B ⊔ E).mkQ.ker ↔ x.val ∈ B
  rw [Submodule.ker_mkQ]
  constructor
  · intro hx
    have h : x.val ∈ A ⊓ (B ⊔ E) := ⟨x.property,hx⟩
    rw [mixed_intersection_of_disjoint A B E hE] at h
    exact h.2
  · intro hx
    exact (show B ≤ B ⊔ E from le_sup_left) hx

/-- The left term embeds in the actual mixed quotient with exactly its
pre-existing scalar relations. -/
def mixedQuotientInjection (A B E : Submodule K V) (hE : Disjoint E (A ⊔ B)) :
    (A ⧸ B.comap A.subtype) →ₗ[K] V ⧸ (B ⊔ E) :=
  (B.comap A.subtype).liftQ (mixedRelationMap A B E)
    (mixedRelationMap_kernel A B E hE).ge

theorem mixedQuotientInjection_injective (A B E : Submodule K V)
    (hE : Disjoint E (A ⊔ B)) : Function.Injective (mixedQuotientInjection A B E hE) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (mixedRelationMap_kernel A B E hE).le

theorem mixedQuotientInjection_range (A B E : Submodule K V)
    (hE : Disjoint E (A ⊔ B)) :
    (mixedQuotientInjection A B E hE).range=A.map (B ⊔ E).mkQ := by
  rw [mixedQuotientInjection,Submodule.range_liftQ,mixedRelationMap,
    LinearMap.range_comp,Submodule.range_subtype]

/-- The right quotient is the literal quotient after both old relation
spaces and the new family have been removed. -/
def mixedQuotientProjection (A B E : Submodule K V) :
    (V ⧸ (B ⊔ E)) →ₗ[K] V ⧸ ((A ⊔ B) ⊔ E) :=
  (B ⊔ E).mapQ ((A ⊔ B) ⊔ E) LinearMap.id (by
    intro x hx
    exact (show B ⊔ E ≤ (A ⊔ B) ⊔ E from
      sup_le (le_sup_of_le_left le_sup_right) le_sup_right) hx)

theorem mixedQuotientProjection_surjective (A B E : Submodule K V) :
    Function.Surjective (mixedQuotientProjection A B E) := by
  intro y
  obtain ⟨x,rfl⟩ := ((A ⊔ B) ⊔ E).mkQ_surjective y
  exact ⟨(B ⊔ E).mkQ x,rfl⟩

theorem mixedQuotientProjection_kernel (A B E : Submodule K V) :
    (mixedQuotientProjection A B E).ker=A.map (B ⊔ E).mkQ := by
  rw [mixedQuotientProjection,Submodule.ker_mapQ,Submodule.comap_id]
  have hB : B.map (B ⊔ E).mkQ=⊥ := by
    apply le_antisymm _ bot_le
    rw [Submodule.map_le_iff_le_comap,Submodule.comap_bot,Submodule.ker_mkQ]
    exact le_sup_left
  have hE : E.map (B ⊔ E).mkQ=⊥ := by
    apply le_antisymm _ bot_le
    rw [Submodule.map_le_iff_le_comap,Submodule.comap_bot,Submodule.ker_mkQ]
    exact le_sup_right
  rw [Submodule.map_sup,Submodule.map_sup,hB,hE,sup_bot_eq,sup_bot_eq]

/-- Exactness of the mixed-row quotient sequence. -/
theorem mixedQuotient_exact (A B E : Submodule K V) (hE : Disjoint E (A ⊔ B)) :
    (mixedQuotientInjection A B E hE).range=(mixedQuotientProjection A B E).ker := by
  rw [mixedQuotientInjection_range,mixedQuotientProjection_kernel]

theorem mixedQuotient_finrank [FiniteDimensional K V]
    (A B E : Submodule K V) (hE : Disjoint E (A ⊔ B)) :
    finrank K (V ⧸ (B ⊔ E)) =
      finrank K (A ⧸ B.comap A.subtype)+finrank K (V ⧸ ((A ⊔ B) ⊔ E)) := by
  have hr := (mixedQuotientProjection A B E).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (mixedQuotientProjection_surjective A B E),
    finrank_top,← mixedQuotient_exact A B E hE,
    LinearMap.finrank_range_of_inj (mixedQuotientInjection_injective A B E hE)] at hr
  omega

end Froberg
