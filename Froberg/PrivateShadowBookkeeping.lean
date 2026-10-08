import Froberg.DisjointShadowSum

/-! Exact finite shadow accounting for an injectively indexed collection of
private source fibers. -/
noncomputable section
namespace Froberg.ShadowDeletion
open Finset
variable {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J] [DecidableEq P]

def regularPart (p : P ↪ I) (ell : I → ℕ) (i : I) : ℕ :=
  if i ∈ univ.map p then 0 else ell i

lemma regularPart_le (p : P ↪ I) (ell : I → ℕ) (i : I) :
    regularPart p ell i ≤ ell i := by
  unfold regularPart
  split_ifs <;> omega

lemma regularPart_positive_not_private (p : P ↪ I) (ell : I → ℕ) (i : I)
    (hi : 0 < regularPart p ell i) : i ∉ univ.map p := by
  intro hp
  simp only [regularPart,ite_eq_left hp,lt_self_iff_false] at hi

lemma sum_regularPart (p : P ↪ I) (ell : I → ℕ) :
    (∑ i,regularPart p ell i)+(∑ j,ell (p j))=∑ i,ell i := by
  have he : (∑ i,regularPart p ell i)=∑ i ∈ univ\univ.map p,ell i := by
    simp only [regularPart,sum_ite,sum_const_zero,zero_add]
    congr 1
    ext i
    simp
  rw [he]
  have hm : (∑ i ∈ univ.map p,ell i)=∑ j,ell (p j) := by rw [sum_map]
  rw [← hm]
  exact sum_sdiff (subset_univ _)

lemma private_shadow_bookkeeping (rel : I → J → Prop) [DecidableRel rel]
    (p : P ↪ I) (ell : I → ℕ) (cold cnew : J → ℕ)
    (B : Finset J) (G : P → Finset J) (C H : ℕ)
    (hcold : ∀ j,cold j ≤ H)
    (hC : ∀ i,i ∉ univ.map p → (B.filter (rel i)).card ≤ C)
    (hcap : ∀ j,j∉B → cold j ≤ cnew j)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (hGB : ∀ i,G i ⊆ B)
    (hprivate : ∀ i j,j∈G i → rel (p i) j ∧ ell (p i) ≤ cnew j) :
    (∑ j,shadow rel (regularPart p ell) cold j)+(∑ i,(G i).card*ell (p i)) ≤
      (∑ j,shadow rel ell cnew j)+H*C*(∑ i,regularPart p ell i) := by
  have hloss := retained_shadow_bound rel (regularPart p ell) cold B C H hcold
    (fun i hi => hC i (regularPart_positive_not_private p ell i hi))
  have hretained := disjoint_shadow_sum B G hG hGB
    (shadow rel (regularPart p ell) cold) (shadow rel ell cnew) (fun i => ell (p i))
    (by
      intro j hj
      unfold shadow
      apply Finset.sup_le
      intro i _
      split_ifs with hij
      · exact (min_le_min (regularPart_le p ell i) (hcap j hj)).trans
          (min_le_shadow rel ell cnew i j hij)
      · exact Nat.zero_le _)
    (by
      intro i j hj
      have hi := hprivate i j hj
      simpa only [min_eq_left hi.2] using min_le_shadow rel ell cnew (p i) j hi.1)
  omega

end Froberg.ShadowDeletion
