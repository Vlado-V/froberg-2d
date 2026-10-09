module

public import Froberg.PrivateColumns
public import Froberg.MixedRestriction

@[expose] public section

/-! Injectivity and exact quotient dimensions after adjoining finitely many
columns on distinct free variables. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module OuterInjection
variable {a z s k b h : ℕ}

def attachedDivisorEquiv (ι : Fin b ↪ Fin z) (β : Fin (a+z) →₀ ℕ) :
    {i : Labels k a s ⊕ Fin b // attachedExponent ι i ≤ β} ≃
      {i : Labels k a s // coreExponent z i ≤ β} ⊕
      {i : Fin b // privateExponent a s ι i ≤ β} where
  toFun i := match i with
    | ⟨Sum.inl j,hj⟩ => Sum.inl ⟨j,hj⟩
    | ⟨Sum.inr j,hj⟩ => Sum.inr ⟨j,hj⟩
  invFun i := match i with
    | Sum.inl ⟨j,hj⟩ => ⟨Sum.inl j,hj⟩
    | Sum.inr ⟨j,hj⟩ => ⟨Sum.inr j,hj⟩
  left_inv i := by rcases i with ⟨i,hi⟩; cases i <;> rfl
  right_inv i := by cases i <;> rfl

lemma card_attached_divisors (ι : Fin b ↪ Fin z) (β : Fin (a+z) →₀ ℕ) :
    Fintype.card {i : Labels k a s ⊕ Fin b // attachedExponent ι i ≤ β} =
      Fintype.card {i : Labels k a s // coreExponent z i ≤ β} +
        (privateDivisors (s := s) ι β).card := by
  classical
  rw [Fintype.card_congr (attachedDivisorEquiv ι β), Fintype.card_sum]
  simp only [Fintype.card_subtype,privateDivisors]

lemma card_attached_divisors_le (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (hh : k*(2*s+1).choose s ≤ h) (hsmall : k*(s+1)+2 ≤ h)
    (β : Fin (a+z) →₀ ℕ) (hβ : β.degree ≤ 2*s+1) :
    Fintype.card {i : Labels k a s ⊕ Fin b // attachedExponent ι i ≤ β} ≤ h := by
  classical
  rw [card_attached_divisors]
  by_cases hp : (privateDivisors (s := s) ι β).Nonempty
  · obtain ⟨i,hi⟩ := hp
    have hd := core_degree_add_private_le ι i β (mem_filter.mp hi).2
    have hc : (corePart β).degree ≤ s+1 := by omega
    have hcore := (card_target_labels_le_core (k := k) (s := s) z β).trans
      (Nat.mul_le_mul_left k (Nat.choose_le_choose s hc))
    have hn := privateDivisors_degree_bound (s := s) ι β
    have htwo : (privateDivisors (s := s) ι β).card ≤ 2 := by nlinarith
    rw [Nat.choose_succ_self_right] at hcore
    omega
  · have he : privateDivisors (s := s) ι β = ∅ := not_nonempty_iff_eq_empty.mp hp
    rw [he,card_empty,add_zero]
    exact (card_target_labels_le (k := k) (s := s) z β).trans
      ((Nat.mul_le_mul_left k (Nat.choose_le_choose s hβ)).trans hh)

lemma attached_fiber_independent {K : Type*} [Field K]
    (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (hh : k*(2*s+1).choose s ≤ h) (hsmall : k*(s+1)+2 ≤ h)
    (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b), U.card ≤ h →
      LinearIndependent K (fun i : U => u i.val))
    (β : Fin (a+z) →₀ ℕ) (hβ : β.degree ≤ 2*s+1) :
    LinearIndependent K (fun i : {i : Labels k a s ⊕ Fin b // attachedExponent ι i ≤ β} => u i.val) := by
  classical
  let U := univ.filter (fun i : Labels k a s ⊕ Fin b => attachedExponent ι i ≤ β)
  have hU : U.card ≤ h := by
    simpa only [Fintype.card_subtype] using card_attached_divisors_le hs ι hh hsmall β hβ
  let f : {i : Labels k a s ⊕ Fin b // attachedExponent ι i ≤ β} → U := fun i =>
    ⟨i.val,mem_filter.mpr ⟨mem_univ _,i.property⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg (fun x : U => x.val) hij)
  exact (hu U hU).comp f hf

lemma attached_multiplication_injective {K : Type*} [Field K]
    (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (hh : k*(2*s+1).choose s ≤ h) (hsmall : k*(s+1)+2 ≤ h)
    (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b), U.card ≤ h →
      LinearIndependent K (fun i : U => u i.val)) :
    ∀ c ≤ s+1, Function.Injective (AttachedMultiplication.multiplication (d := c)
      (attachedExponent ι) u) := by
  intro c hc
  apply AttachedMultiplication.injective_of_independent_fibers (attachedExponent ι) u
    (attachedExponent_degree ι)
  intro β hβ
  exact attached_fiber_independent hs ι hh hsmall u hu β (by omega)

lemma attached_quotient_finrank {K : Type*} [Field K]
    (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (hh : k*(2*s+1).choose s ≤ h) (hsmall : k*(s+1)+2 ≤ h)
    (u : Labels k a s ⊕ Fin b → Fin h → K)
    (hu : ∀ U : Finset (Labels k a s ⊕ Fin b), U.card ≤ h →
      LinearIndependent K (fun i : U => u i.val))
    (hn : 0 < a+z) (c : ℕ) (hc : c ≤ s+1) :
    finrank K ((Fin h → Forms K (a+z) (s+c)) ⧸
      AttachedMultiplication.relationSpace (d := c) (attachedExponent ι) u (attachedExponent_degree ι)) =
      h*(a+z+(s+c)-1).choose (s+c) -
        (Fintype.card (Labels k a s)+b)*(a+z+c-1).choose c := by
  simpa only [Fintype.card_fin,Fintype.card_sum] using
    AttachedMultiplication.quotient_finrank_of_injective (attachedExponent ι) u
      (attachedExponent_degree ι) hn (attached_multiplication_injective hs ι hh hsmall u hu c hc)

end Froberg.PrivateColumns
