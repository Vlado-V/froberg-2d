module

public import Froberg.PrivateMultiplierCounts
public import Froberg.PrivateFibers
public import Froberg.PrivateTargetDeletion

@[expose] public section

/-! Disjoint target sets on which private source fibers multiply identically. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset MonomialExpansion OuterInjection
variable {a z s b : ℕ}

def privateTargetEmbedding (ι : Fin b ↪ Fin z) (i : Fin b) :
    Degree (a+z) (s+1) ↪ Degree (a+z) (2*s+1) where
  toFun γ := ⟨privateExponent a s ι i+γ.val,mem_exponents.mpr (by
    rw [map_add,privateExponent_degree,degree_val]
    omega)⟩
  inj' := by
    intro γ δ he
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val he)

def privateGoodTargets (ι : Fin b ↪ Fin z) (i : Fin b) :
    Finset (Degree (a+z) (2*s+1)) :=
  (privateGoodMultipliers a s ι).map (privateTargetEmbedding ι i)

@[simp] lemma privateGoodTargets_card (ι : Fin b ↪ Fin z) (i : Fin b) :
    (privateGoodTargets (a := a) (s := s) ι i).card=(privateGoodMultipliers a s ι).card := card_map _

lemma privateGoodTargets_properties (hs : 0 < s) (ι : Fin b ↪ Fin z)
    (i : Fin b) {β : Degree (a+z) (2*s+1)} (hβ : β∈privateGoodTargets (a := a) (s := s) ι i) :
    (corePart β.val).degree < s ∧ privateExponent a s ι i ≤ β.val ∧
      ∀ j, privateExponent a s ι j ≤ β.val → j=i := by
  obtain ⟨γ,hγ,rfl⟩ := mem_map.mp hβ
  have hdiv := privateGoodMultipliers_unique_divisor ι i hγ
  have hcore := (mem_filter.mp (mem_filter.mp hγ).1).2
  have hc : corePart (privateExponent a s ι i+γ.val)=corePart γ.val := by
    ext j
    change (privateExponent a s ι i+γ.val) (Fin.castAdd z j)=γ.val (Fin.castAdd z j)
    have hz := congrArg (fun x : Fin a →₀ ℕ => x j) (privateExponent_core (a := a) (s := s) ι i)
    simp only [corePart_apply,Finsupp.zero_apply] at hz
    simp only [Finsupp.add_apply,hz,zero_add]
  refine ⟨?_,le_add_right le_rfl,?_⟩
  · change (corePart (privateExponent a s ι i+γ.val)).degree < s
    rw [hc]
    omega
  · intro j hj
    have hjmem : j∈privateDivisors (s := s) ι (privateExponent a s ι i+γ.val) :=
      mem_filter.mpr ⟨mem_univ _,hj⟩
    simpa only [hdiv,mem_singleton] using hjmem

lemma privateGoodTargets_subset_bad (ι : Fin b ↪ Fin z) (i : Fin b) :
    privateGoodTargets (a := a) (s := s) ι i ⊆ badTargets (s := s) ι := by
  intro β hβ
  obtain ⟨γ,hγ,rfl⟩ := mem_map.mp hβ
  exact mem_filter.mpr ⟨mem_univ _,i,le_add_right le_rfl⟩

lemma privateGoodTargets_disjoint (hs : 0 < s) (ι : Fin b ↪ Fin z) :
    Pairwise (fun i j => Disjoint (privateGoodTargets (a := a) (s := s) ι i) (privateGoodTargets (a := a) (s := s) ι j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro β hβi hβj
  have hi := privateGoodTargets_properties hs ι i hβi
  have hj := privateGoodTargets_properties hs ι j hβj
  exact hij (hi.2.2 j hj.2.1).symm

end Froberg.PrivateColumns
