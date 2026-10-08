import Froberg.CoreDivisors

/-! Exact coordinates for monomials of a fixed degree in two variable blocks. -/
noncomputable section
namespace Froberg.OuterInjection
open Finset

/-- Restriction to the complementary block of variables. -/
def freePart {a z : ℕ} (β : Fin (a + z) →₀ ℕ) : Fin z →₀ ℕ :=
  β.comapDomain (Fin.natAdd a) (Fin.natAdd_injective z a).injOn

@[simp] theorem freePart_apply {a z : ℕ} (β : Fin (a + z) →₀ ℕ) (i : Fin z) :
    freePart β i = β (Fin.natAdd a i) := rfl

/-- Join two exponent vectors in disjoint variable blocks. -/
def joinParts {a z : ℕ} (α : Fin a →₀ ℕ) (γ : Fin z →₀ ℕ) : Fin (a + z) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.addCases α γ)

@[simp] theorem joinParts_core {a z : ℕ} (α : Fin a →₀ ℕ) (γ : Fin z →₀ ℕ) (i : Fin a) :
    joinParts α γ (Fin.castAdd z i) = α i := by simp [joinParts]

@[simp] theorem joinParts_free {a z : ℕ} (α : Fin a →₀ ℕ) (γ : Fin z →₀ ℕ) (i : Fin z) :
    joinParts α γ (Fin.natAdd a i) = γ i := by simp [joinParts]

@[simp] theorem corePart_joinParts {a z : ℕ} (α : Fin a →₀ ℕ) (γ : Fin z →₀ ℕ) :
    corePart (joinParts α γ) = α := by ext i; simp

@[simp] theorem freePart_joinParts {a z : ℕ} (α : Fin a →₀ ℕ) (γ : Fin z →₀ ℕ) :
    freePart (joinParts α γ) = γ := by ext i; simp

@[simp] theorem joinParts_parts {a z : ℕ} (β : Fin (a + z) →₀ ℕ) :
    joinParts (corePart β) (freePart β) = β := by
  ext i
  induction i using Fin.addCases <;> simp

theorem degree_parts {a z : ℕ} (β : Fin (a + z) →₀ ℕ) :
    (corePart β).degree + (freePart β).degree = β.degree := by
  simp only [Finsupp.degree_eq_sum, Fin.sum_univ_add, corePart_apply, freePart_apply]

theorem degree_joinParts {a z : ℕ} (α : Fin a →₀ ℕ) (γ : Fin z →₀ ℕ) :
    (joinParts α γ).degree = α.degree + γ.degree := by
  rw [← degree_parts, corePart_joinParts, freePart_joinParts]

theorem corePart_le_degree {a z : ℕ} (β : Fin (a + z) →₀ ℕ) :
    (corePart β).degree ≤ β.degree := by have := degree_parts β; omega

theorem joinParts_le_joinParts {a z : ℕ} (α α' : Fin a →₀ ℕ) (γ γ' : Fin z →₀ ℕ) :
    joinParts α γ ≤ joinParts α' γ' ↔ α ≤ α' ∧ γ ≤ γ' := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd z i),
      fun i => by simpa using h (Fin.natAdd a i)⟩
  · rintro ⟨ha, hz⟩ i
    induction i using Fin.addCases with
    | left i => simpa using ha i
    | right i => simpa using hz i

/-- The actual monomials of a fixed bidegree are a product of monomial sets. -/
def bidegreeEquiv (a z r i : ℕ) (hi : i ≤ r) :
    {β : MonomialExpansion.Degree (a + z) r // (corePart β.val).degree = i} ≃
      MonomialExpansion.Degree a i × MonomialExpansion.Degree z (r - i) where
  toFun β :=
    (⟨corePart β.val.val, MonomialExpansion.mem_exponents.mpr β.property⟩,
     ⟨freePart β.val.val, MonomialExpansion.mem_exponents.mpr (by
       have h := degree_parts β.val.val
       have hb := MonomialExpansion.degree_val β.val
       have hc := β.property
       omega)⟩)
  invFun p := ⟨⟨joinParts p.1.val p.2.val, MonomialExpansion.mem_exponents.mpr (by
    rw [degree_joinParts, MonomialExpansion.degree_val, MonomialExpansion.degree_val]
    omega)⟩, by simp [MonomialExpansion.degree_val]⟩
  left_inv β := by apply Subtype.ext; apply Subtype.ext; exact joinParts_parts β.val.val
  right_inv p := by apply Prod.ext <;> apply Subtype.ext <;> simp

theorem card_bidegree (a z r i : ℕ) (hi : i ≤ r) :
    Fintype.card {β : MonomialExpansion.Degree (a + z) r // (corePart β.val).degree = i} =
      (a + i - 1).choose i * (z + (r - i) - 1).choose (r - i) := by
  rw [Fintype.card_congr (bidegreeEquiv a z r i hi), Fintype.card_prod,
    MonomialExpansion.card_degree, MonomialExpansion.card_degree]

end Froberg.OuterInjection
