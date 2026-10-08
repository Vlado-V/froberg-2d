import Froberg.ShadowDeletion

/-! Add independently retained regular and private target contributions. -/
noncomputable section
namespace Froberg.ShadowDeletion
open Finset
variable {J P : Type*} [Fintype J] [Fintype P] [DecidableEq J] [DecidableEq P]

lemma disjoint_shadow_sum (B : Finset J) (G : P → Finset J)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hGB : ∀ i,G i ⊆ B) (regular actual : J → ℕ) (l : P → ℕ)
    (hr : ∀ j,j∉B → regular j ≤ actual j)
    (hp : ∀ i j,j∈G i → l i ≤ actual j) :
    (∑ j ∈ univ\B,regular j)+(∑ i,(G i).card*l i) ≤ ∑ j,actual j := by
  let U := univ.biUnion G
  have hU : U ⊆ B := by
    intro j hj
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hj
    exact hGB i hi
  have hdis : Disjoint (univ\B) U := by
    apply disjoint_left.mpr
    intro j hj hju
    exact (mem_sdiff.mp hj).2 (hU hju)
  have hregular : (∑ j ∈ univ\B,regular j) ≤ ∑ j ∈ univ\B,actual j :=
    sum_le_sum (fun j hj => hr j (mem_sdiff.mp hj).2)
  have hprivate : (∑ i,(G i).card*l i) ≤ ∑ j ∈ U,actual j := by
    rw [show U=univ.biUnion G from rfl,sum_biUnion]
    · apply sum_le_sum
      intro i _
      calc
        (G i).card*l i = ∑ j ∈ G i,l i := by simp
        _ ≤ ∑ j ∈ G i,actual j := sum_le_sum (fun j hj => hp i j hj)
    · intro i hi j hj hij
      exact hG hij
  have htot : (∑ j ∈ univ\B,actual j)+(∑ j ∈ U,actual j) ≤ ∑ j,actual j := by
    rw [← sum_union hdis]
    exact sum_le_sum_of_subset (subset_univ _)
  omega

end Froberg.ShadowDeletion
