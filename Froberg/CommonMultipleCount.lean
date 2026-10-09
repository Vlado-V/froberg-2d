module

public import Froberg.MonomialIncidence

@[expose] public section

/-! A fixed additional source monomial affects only O(m^s) target monomials. -/
noncomputable section
namespace Froberg.MonomialExpansion

/-- Comparable monomials of the same degree are equal. -/
theorem eq_of_le_of_degree_eq {n : ℕ} {a b : Fin n →₀ ℕ}
    (hab : a ≤ b) (hd : a.degree = b.degree) : a = b := by
  have he : a + (b-a) = b := add_tsub_cancel_of_le hab
  have hz : (b-a).degree = 0 := by
    have hh := congrArg Finsupp.degree he
    rw [map_add,hd] at hh
    omega
  have hzero := (Finsupp.degree_eq_zero_iff (b-a)).mp hz
  simpa only [hzero,add_zero] using he

/-- Distinct degree-s monomials have least common multiple of degree at least s+1. -/
theorem degree_sup_ge_succ {n s : ℕ} {a b : Fin n →₀ ℕ}
    (ha : a.degree = s) (hb : b.degree = s) (hne : a ≠ b) :
    s+1 ≤ (a ⊔ b).degree := by
  have hlo : s ≤ (a ⊔ b).degree := ha ▸ Finsupp.degree_mono le_sup_left
  have hneq : (a ⊔ b).degree ≠ s := by
    intro he
    have h1 : a = a ⊔ b := eq_of_le_of_degree_eq le_sup_left (ha.trans he.symm)
    have h2 : b = a ⊔ b := eq_of_le_of_degree_eq le_sup_right (hb.trans he.symm)
    exact hne (h1.trans h2.symm)
  omega

/-- All degree-(2s+1) multiples of one monomial of degree at least s+1
number at most the degree-s monomials. -/
theorem card_targets_above_le {n s : ℕ} (hn : 0 < n) (p : Fin n →₀ ℕ)
    (hp : s+1 ≤ p.degree) (T : Finset (Fin n →₀ ℕ))
    (hT : ∀ b ∈ T, b.degree = 2*s+1 ∧ p ≤ b) :
    T.card ≤ (n+s-1).choose s := by
  classical
  let d := 2*s+1-p.degree
  have hd : d ≤ s := by omega
  have hmap : T.image (fun b => b-p) ⊆ exponents n d := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hbd,hpb⟩ := hT b hb
    have hh := congrArg Finsupp.degree (add_tsub_cancel_of_le hpb)
    rw [map_add,hbd] at hh
    apply mem_exponents.mpr
    dsimp [d]
    omega
  have hi : Set.InjOn (fun b : Fin n →₀ ℕ => b-p) T := by
    intro a ha b hb he
    have ha' := add_tsub_cancel_of_le (hT a ha).2
    have hb' := add_tsub_cancel_of_le (hT b hb).2
    exact ha'.symm.trans ((congrArg (fun c => p+c) he).trans hb')
  calc
    T.card = (T.image (fun b => b-p)).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ (exponents n d).card := Finset.card_le_card hmap
    _ = (n+d-1).choose d := card_exponents n d
    _ ≤ (n+s-1).choose s := by
      rw [← Nat.choose_symm (by omega : d ≤ n+d-1),
        ← Nat.choose_symm (by omega : s ≤ n+s-1)]
      have he1 : n+d-1-d = n-1 := by omega
      have he2 : n+s-1-s = n-1 := by omega
      rw [he1,he2]
      exact Nat.choose_le_choose (n-1) (by omega)

/-- Two distinct source monomials therefore have at most this many common targets. -/
theorem card_common_targets_le {n s : ℕ} (hn : 0 < n) (a b : Fin n →₀ ℕ)
    (ha : a.degree = s) (hb : b.degree = s) (hne : a ≠ b)
    (T : Finset (Fin n →₀ ℕ))
    (hT : ∀ c ∈ T, c.degree = 2*s+1 ∧ a ≤ c ∧ b ≤ c) :
    T.card ≤ (n+s-1).choose s :=
  card_targets_above_le hn (a ⊔ b) (degree_sup_ge_succ ha hb hne) T
    (fun c hc => ⟨(hT c hc).1,sup_le (hT c hc).2.1 (hT c hc).2.2⟩)

end Froberg.MonomialExpansion
