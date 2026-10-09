module

public import Froberg.MonomialIncidence

@[expose] public section

/-! Counting the repeated-variable error between exact and squarefree
coarse monomial capacities. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Finset

lemma weight_squarefree {n : ℕ} (b a : Fin n →₀ ℕ) (hb : ∀ i, b i ≤ 1) :
    weight b a = if a ≤ b then 1 else 0 := by
  classical
  split_ifs with hab
  · have hchoose (i : Fin n) : (b i).choose (a i) = 1 := by
      have hbi := hb i
      have hai := hab i
      have hb' : b i = 0 ∨ b i = 1 := by omega
      rcases hb' with h0 | h1
      · have ha0 : a i = 0 := by omega
        simp [h0, ha0]
      · have ha' : a i = 0 ∨ a i = 1 := by omega
        rcases ha' with ha' | ha' <;> simp [h1, ha']
    simp [weight, hchoose]
  · exact Classical.not_not.mp (mt (weight_ne_zero_iff b a).mp hab)

lemma card_divisors_squarefree {n : ℕ} (b : Fin n →₀ ℕ) (e : ℕ) (hb : ∀ i, b i ≤ 1) :
    Fintype.card (Divisor b e) = b.degree.choose e := by
  classical
  rw [← sum_weight_sources b e]
  simp only [weight_squarefree b _ hb, sum_boole]
  exact Fintype.card_coe _

lemma single_two_le {n : ℕ} (b : Fin n →₀ ℕ) (i : Fin n) (hi : 2 ≤ b i) :
    Finsupp.single i 2 ≤ b := by
  intro j
  by_cases hij : i = j
  · subst j
    simpa using hi
  · simp [Finsupp.single_apply, hij, Ne.symm hij]

lemma degree_remove_two {n r : ℕ} (b : Degree n r) (i : Fin n) (hi : 2 ≤ b.val i) :
    (b.val - Finsupp.single i 2).degree = r - 2 := by
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le (single_two_le b.val i hi))
  simp only [map_add, Finsupp.degree_single, degree_val] at h
  omega

/-- Repeated-variable monomials embed into a chosen repeated variable
and a monomial two degrees lower. -/
def repetitionEmbedding (n r : ℕ) :
    {b : Degree n r // ∃ i, 2 ≤ b.val i} ↪ Fin n × Degree n (r - 2) where
  toFun b :=
    let i := Classical.choose b.property
    (i, ⟨b.val.val - Finsupp.single i 2,
      mem_exponents.mpr (degree_remove_two b.val i (Classical.choose_spec b.property))⟩)
  inj' := by
    intro b c h
    have hi := congrArg Prod.fst h
    have hr := congrArg (fun p : Fin n × Degree n (r - 2) => p.2.val) h
    dsimp only at hi hr
    apply Subtype.ext
    apply Subtype.ext
    have hb := tsub_add_cancel_of_le
      (single_two_le b.val.val (Classical.choose b.property) (Classical.choose_spec b.property))
    have hc := tsub_add_cancel_of_le
      (single_two_le c.val.val (Classical.choose c.property) (Classical.choose_spec c.property))
    rw [hi] at hb hr
    exact hb.symm.trans ((congrArg (fun v => v + Finsupp.single (Classical.choose c.property) 2) hr).trans hc)

lemma card_repeated_monomials (n r : ℕ) :
    Fintype.card {b : Degree n r // ∃ i, 2 ≤ b.val i} ≤
      n * (n + (r - 2) - 1).choose (r - 2) := by
  have h := Fintype.card_le_of_embedding (repetitionEmbedding n r)
  simpa only [Fintype.card_prod, Fintype.card_fin, card_degree] using h

end Froberg.MonomialExpansion
