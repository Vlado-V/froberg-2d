module

public import Froberg.PrivateColumns
public import Froberg.CommonMultipleCount

@[expose] public section

/-! Exact fiber relations on the retained regular and private targets. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module OuterInjection AttachedMultiplication
variable {K : Type*} [Field K] {a z s k b h : ℕ}

lemma core_relation_eq_bot_of_degree_lt (v : Labels k a s → Fin h → K)
    (β : Fin (a+z) →₀ ℕ) (hc : (corePart β).degree < s) :
    relationFiber (coreExponent z) v β = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  have hi := Finsupp.degree_mono ((coreExponent_le_iff i.val β).mp i.property)
  rw [(exponentEquiv a s i.val.2).property] at hi
  omega

lemma relationFiber_regular (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (β : Fin (a+z) →₀ ℕ) (hp : ∀ i, ¬privateExponent a s ι i ≤ β) :
    relationFiber (attachedExponent ι) (attachedVectors v w) β =
      relationFiber (coreExponent z) v β := by
  rw [relationFiber_attached]
  have hz : Submodule.span K (Set.range (fun i : {i : Fin b // privateExponent a s ι i ≤ β} => w i.val)) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact False.elim (hp i.val i.property)
  rw [hz,sup_bot_eq]

lemma relationFiber_good_private (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (i : Fin b) (β : Fin (a+z) →₀ ℕ) (hc : (corePart β).degree < s)
    (hi : privateExponent a s ι i ≤ β)
    (hj : ∀ j, privateExponent a s ι j ≤ β → j=i) :
    relationFiber (attachedExponent ι) (attachedVectors v w) β =
      Submodule.span K {w i} := by
  rw [relationFiber_attached,core_relation_eq_bot_of_degree_lt v β hc,bot_sup_eq]
  congr 1
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    change w j.val ∈ {w i}
    rw [hj j.val j.property]
    exact Set.mem_singleton _
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨⟨i,hi⟩,hx.symm⟩

lemma relationFiber_private_source (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K) (i : Fin b) :
    relationFiber (attachedExponent ι) (attachedVectors v w) (privateExponent a s ι i) =
      Submodule.span K {w i} := by
  apply relationFiber_good_private ι v w i
  · simpa only [privateExponent_core,map_zero] using hs
  · exact le_rfl
  · intro j hj
    apply privateExponent_injective hs ι
    exact MonomialExpansion.eq_of_le_of_degree_eq hj
      ((privateExponent_degree ι j).trans (privateExponent_degree ι i).symm)

lemma private_good_capacity (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K)
    (i : Fin b) (β : Fin (a+z) →₀ ℕ) (hc : (corePart β).degree < s)
    (hi : privateExponent a s ι i ≤ β)
    (hj : ∀ j, privateExponent a s ι j ≤ β → j=i) :
    finrank K ((Fin h → K) ⧸ relationFiber (attachedExponent ι) (attachedVectors v w) β) =
      finrank K ((Fin h → K) ⧸ relationFiber (attachedExponent ι) (attachedVectors v w)
        (privateExponent a s ι i)) := by
  rw [relationFiber_good_private ι v w i β hc hi hj,relationFiber_private_source hs ι v w i]

end Froberg.PrivateColumns
