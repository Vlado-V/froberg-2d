import Froberg.PrivateColumns

/-! Exact finite counting of the multipliers reserved for private columns. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset OuterInjection MonomialExpansion

/-- Removing a fixed monomial identifies its divisible multiples with the residual degree. -/
def divisibleDegreeEquiv {n s t : ℕ} (α : Fin n →₀ ℕ) (hα : α.degree=s) :
    {β : Degree n (s+t) // α≤β.val} ≃ Degree n t where
  toFun β := ⟨β.val.val-α, mem_exponents.mpr (by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le β.property)
    rw [map_add, hα, degree_val] at h
    omega)⟩
  invFun γ := ⟨⟨γ.val+α, mem_exponents.mpr (by rw [map_add,degree_val,hα]; omega)⟩,
    by exact le_add_left le_rfl⟩
  left_inv β := by apply Subtype.ext; apply Subtype.ext; exact tsub_add_cancel_of_le β.property
  right_inv γ := by apply Subtype.ext; simp

theorem card_divisible_degree {n s t : ℕ} (α : Fin n →₀ ℕ) (hα : α.degree=s) :
    Fintype.card {β : Degree n (s+t) // α≤β.val} = (n+t-1).choose t := by
  rw [Fintype.card_congr (divisibleDegreeEquiv α hα),card_degree]

def coreGoodMultipliers (a z s : ℕ) : Finset (Degree (a+z) (s+1)) :=
  univ.filter (fun γ => (corePart γ.val).degree≤ s-1)

theorem coreGoodMultipliers_card (a z : ℕ) {s : ℕ} (hs : 0<s) :
    (coreGoodMultipliers a z s).card + (a+(s+1)-1).choose (s+1) +
      z*(a+s-1).choose s = (a+z+(s+1)-1).choose (s+1) := by
  let S : Finset (Degree (a+z) (s+1)) := univ.filter (fun γ => (corePart γ.val).degree=s)
  let T : Finset (Degree (a+z) (s+1)) := univ.filter (fun γ => (corePart γ.val).degree=s+1)
  have hS : S.card=(a+s-1).choose s*z := by
    have h := card_bidegree a z (s+1) s (by omega)
    simpa only [Fintype.card_subtype, show s+1-s=1 by omega, Nat.add_sub_cancel,
      Nat.choose_one_right] using h
  have hT : T.card=(a+(s+1)-1).choose (s+1) := by
    have h := card_bidegree a z (s+1) (s+1) le_rfl
    simpa only [Fintype.card_subtype, Nat.sub_self, Nat.choose_zero_right, mul_one] using h
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    intro γ hγS hγT
    have hs' := (mem_filter.mp hγS).2
    have ht' := (mem_filter.mp hγT).2
    omega
  have hbad : (univ.filter (fun γ : Degree (a+z) (s+1) =>
      ¬(corePart γ.val).degree≤ s-1)) = S∪T := by
    ext γ
    have hdeg : (corePart γ.val).degree≤ s+1 := by
      simpa only [degree_val] using corePart_le_degree γ.val
    simp only [mem_filter, mem_univ, true_and, mem_union, S, T]
    omega
  have hpartition := card_filter_add_card_filter_not
    (s := (univ : Finset (Degree (a+z) (s+1)))) (p := fun γ => (corePart γ.val).degree≤ s-1)
  rw [hbad, card_union_of_disjoint hdis, hS, hT, card_univ, card_degree] at hpartition
  rw [Nat.mul_comm ((a+s-1).choose s) z] at hpartition
  change _+_+_=_
  unfold coreGoodMultipliers
  omega

/-- Excluding every private power is a convenient uniform sufficient condition. -/
def privateGoodMultipliers {b : ℕ} (a s : ℕ) {z : ℕ} (ι : Fin b ↪ Fin z) :
    Finset (Degree (a+z) (s+1)) :=
  (coreGoodMultipliers a z s).filter (fun γ => ∀ j, ¬privateExponent a s ι j≤γ.val)

theorem privateGoodMultipliers_card_lower {a z s b : ℕ} (hs : 0<s)
    (ι : Fin b ↪ Fin z) :
    (a+z+(s+1)-1).choose (s+1) ≤ (privateGoodMultipliers a s ι).card +
      (a+(s+1)-1).choose (s+1) + z*(a+s-1).choose s + b*(a+z) := by
  classical
  let B : Fin b → Finset (Degree (a+z) (s+1)) := fun j =>
    univ.filter (fun γ => privateExponent a s ι j≤γ.val)
  have hB (j : Fin b) : (B j).card=a+z := by
    have h := card_divisible_degree (t := 1) (privateExponent a s ι j) (privateExponent_degree ι j)
    simpa only [Fintype.card_subtype,Nat.add_sub_cancel,Nat.choose_one_right] using h
  have hcover : coreGoodMultipliers a z s ⊆ privateGoodMultipliers a s ι ∪ univ.biUnion B := by
    intro γ hγ
    by_cases hp : ∀ j, ¬privateExponent a s ι j≤γ.val
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hp⟩)
    · push_neg at hp
      obtain ⟨j,hj⟩ := hp
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨mem_univ _,hj⟩⟩)
  have hunion : (univ.biUnion B).card≤b*(a+z) := by
    calc
      _ ≤ ∑ j : Fin b, (B j).card := card_biUnion_le
      _ = _ := by simp only [hB,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]
  have hcoverCard := (card_le_card hcover).trans (card_union_le _ _)
  have hcore := coreGoodMultipliers_card a z hs
  omega

/-- The shifted target has just the selected private divisor. -/
theorem privateGoodMultipliers_unique_divisor {a z s b : ℕ}
    (ι : Fin b ↪ Fin z) (i : Fin b) {γ : Degree (a+z) (s+1)}
    (hγ : γ∈privateGoodMultipliers a s ι) :
    privateDivisors (s := s) ι (privateExponent a s ι i+γ.val)={i} := by
  classical
  have hgood := (mem_filter.mp hγ).2
  ext j
  simp only [privateDivisors,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · intro hj
    by_contra hji
    have hne : Fin.natAdd a (ι i) ≠ Fin.natAdd a (ι j) := by
      intro h
      exact hji (ι.injective ((Fin.natAdd_injective z a) h)).symm
    have hj' := (privateExponent_le_iff ι j _).mp hj
    simp only [privateExponent,Finsupp.add_apply,Finsupp.single_eq_of_ne hne.symm,zero_add] at hj'
    exact hgood j ((privateExponent_le_iff ι j _).mpr hj')
  · rintro rfl
    exact le_add_right le_rfl

end Froberg.PrivateColumns
