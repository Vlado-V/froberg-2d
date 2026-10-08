import Froberg.OuterCapacityBounds
import Froberg.BidegreeExponents

/-! The core-attached presentation with fixed columns on distinct free
variables. These are literal polynomial monomials and vector relations. -/
noncomputable section
namespace Froberg.PrivateColumns
open Finset Module OuterInjection

variable {a z s k b h : ℕ}

def privateExponent (a s : ℕ) (ι : Fin b ↪ Fin z) (i : Fin b) : Fin (a+z) →₀ ℕ :=
  Finsupp.single (Fin.natAdd a (ι i)) s

@[simp] lemma privateExponent_degree (ι : Fin b ↪ Fin z) (i : Fin b) :
    (privateExponent a s ι i).degree=s := by simp [privateExponent]

@[simp] lemma privateExponent_core (ι : Fin b ↪ Fin z) (i : Fin b) :
    corePart (privateExponent a s ι i)=0 := by
  ext j
  have hne : Fin.natAdd a (ι i) ≠ Fin.castAdd z j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  simp [privateExponent,corePart_apply,hne]

lemma privateExponent_injective (hs : 0 < s) (ι : Fin b ↪ Fin z) :
    Function.Injective (privateExponent a s ι) := by
  intro i j hij
  apply ι.injective
  apply Fin.natAdd_injective
  exact Finsupp.single_left_injective hs.ne' hij

lemma privateExponent_le_iff (ι : Fin b ↪ Fin z) (i : Fin b) (β : Fin (a+z) →₀ ℕ) :
    privateExponent a s ι i ≤ β ↔ s ≤ β (Fin.natAdd a (ι i)) := by
  simp only [privateExponent,Finsupp.single_le_iff]

def attachedExponent (ι : Fin b ↪ Fin z) : Labels k a s ⊕ Fin b → Fin (a+z) →₀ ℕ :=
  Sum.elim (coreExponent z) (privateExponent a s ι)

@[simp] lemma attachedExponent_degree (ι : Fin b ↪ Fin z) (i : Labels k a s ⊕ Fin b) :
    (attachedExponent ι i).degree=s := by
  cases i with
  | inl i => exact coreExponent_degree z i
  | inr i => exact privateExponent_degree ι i

def attachedVectors {K : Type*} (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K) :
    Labels k a s ⊕ Fin b → Fin h → K := Sum.elim v w

lemma equal_of_le_equal_degree {n : ℕ} {α β : Fin n →₀ ℕ}
    (hle : α ≤ β) (hdeg : α.degree=β.degree) : α=β := by
  have he : α+(β-α)=β := add_tsub_cancel_of_le hle
  have hd := congrArg Finsupp.degree he
  rw [map_add,hdeg] at hd
  have hz : (β-α).degree=0 := by omega
  rw [(Finsupp.degree_eq_zero_iff _).mp hz,add_zero] at he
  exact he

lemma core_degree_add_private_le (ι : Fin b ↪ Fin z) (i : Fin b)
    (β : Fin (a+z) →₀ ℕ) (hi : privateExponent a s ι i ≤ β) :
    (corePart β).degree+s ≤ β.degree := by
  have he : privateExponent a s ι i+(β-privateExponent a s ι i)=β := add_tsub_cancel_of_le hi
  have hd := congrArg Finsupp.degree he
  rw [map_add,privateExponent_degree] at hd
  have hc : corePart β=corePart (β-privateExponent a s ι i) := by
    rw [← he]
    ext j
    simp only [corePart_apply,Finsupp.add_apply]
    have hz := congrArg (fun f : Fin a →₀ ℕ => f j) (privateExponent_core (a := a) (s := s) ι i)
    simp only [corePart_apply,Finsupp.zero_apply] at hz
    rw [hz,zero_add]
    simp only [add_tsub_cancel_left]
  rw [hc]
  have hb := corePart_le_degree (β-privateExponent a s ι i)
  omega

def privateDivisors (ι : Fin b ↪ Fin z) (β : Fin (a+z) →₀ ℕ) : Finset (Fin b) :=
  univ.filter (fun i => privateExponent a s ι i ≤ β)

lemma privateDivisors_degree_bound (ι : Fin b ↪ Fin z) (β : Fin (a+z) →₀ ℕ) :
    (privateDivisors (s := s) ι β).card*s ≤ β.degree := by
  let S := privateDivisors (s := s) ι β
  let f : Fin b → Fin (a+z) := fun i => Fin.natAdd a (ι i)
  have hf : Function.Injective f := (Fin.natAdd_injective z a).comp ι.injective
  calc
    S.card*s = ∑ i ∈ S, s := by simp
    _ ≤ ∑ i ∈ S, β (f i) := by
      apply sum_le_sum
      intro i hi
      exact (privateExponent_le_iff ι i β).mp ((mem_filter.mp hi).2)
    _ = ∑ j ∈ S.image f, β j := by rw [sum_image]; exact fun _ _ _ _ he => hf he
    _ ≤ ∑ j : Fin (a+z), β j := sum_le_sum_of_subset (subset_univ _)
    _ = β.degree := by rw [Finsupp.degree_eq_sum]

lemma privateDivisors_card_le_two (hs : 2 ≤ s) (ι : Fin b ↪ Fin z)
    (β : Fin (a+z) →₀ ℕ) (hβ : β.degree=2*s+1) :
    (privateDivisors (s := s) ι β).card ≤ 2 := by
  have h := privateDivisors_degree_bound (s := s) ι β
  rw [hβ] at h
  nlinarith

lemma private_source_eq (hs : 0 < s) (ι : Fin b ↪ Fin z) (i : Fin b)
    (α : Fin (a+z) →₀ ℕ) (hα : α.degree=s) :
    privateExponent a s ι i ≤ α ↔ α=privateExponent a s ι i := by
  constructor
  · intro h
    exact (equal_of_le_equal_degree h ((privateExponent_degree ι i).trans hα.symm)).symm
  · rintro rfl
    exact le_rfl

lemma relationFiber_attached {K : Type*} [Field K] (ι : Fin b ↪ Fin z)
    (v : Labels k a s → Fin h → K) (w : Fin b → Fin h → K) (β : Fin (a+z) →₀ ℕ) :
    AttachedMultiplication.relationFiber (attachedExponent ι) (attachedVectors v w) β =
      AttachedMultiplication.relationFiber (coreExponent z) v β ⊔
        Submodule.span K (Set.range (fun i : {i : Fin b // privateExponent a s ι i ≤ β} => w i.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rcases i with ⟨i,hi⟩
    cases i with
    | inl i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩)
    | inr i => exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨⟨Sum.inl i.val,i.property⟩,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨⟨Sum.inr i.val,i.property⟩,rfl⟩

end Froberg.PrivateColumns
