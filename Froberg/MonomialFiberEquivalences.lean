import Froberg.MonomialProfileTransport

/-! Identifying the transport's states with actual source monomials and
with the nonzero-capacity target monomials. -/
noncomputable section
namespace Froberg
open MonomialExpansion OuterInjection

def sourceProfileEquiv (s : ℕ) : Option (Fin s) ≃ Fin (s + 1) :=
  (finSuccEquiv' (Fin.last s)).symm

lemma sourceProfileEquiv_val {s : ℕ} (i : Option (Fin s)) :
    (sourceProfileEquiv s i).val = profileSourceIndex i := by
  cases i <;> simp [sourceProfileEquiv, profileSourceIndex, Fin.succAbove_last]

lemma profileSourceIndex_injective (s : ℕ) : Function.Injective (@profileSourceIndex s) := by
  intro i j hij
  apply (sourceProfileEquiv s).injective
  apply Fin.ext
  simpa only [sourceProfileEquiv_val] using hij

def sourceExponent {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i) : Degree (a + z) s :=
  ⟨joinParts α.2.1.val α.2.2.val, mem_exponents.mpr (by
    rw [degree_joinParts, degree_val, degree_val]
    have hi := profileSourceIndex_le α.1
    omega)⟩

lemma sourceExponent_core_degree {a z s : ℕ} (α : Σ i, SourceMonomialFiber a z s i) :
    (corePart (sourceExponent α).val).degree = profileSourceIndex α.1 := by
  simp only [sourceExponent, corePart_joinParts, degree_val]

lemma sourceExponent_injective (a z s : ℕ) : Function.Injective (@sourceExponent a z s) := by
  rintro ⟨i, α⟩ ⟨j, β⟩ h
  have hi : i = j := by
    apply profileSourceIndex_injective s
    have hc := congrArg (fun γ : Degree (a + z) s => (corePart γ.val).degree) h
    simpa only [sourceExponent_core_degree] using hc
  subst j
  have hc := congrArg (fun γ : Degree (a + z) s => corePart γ.val) h
  have hz := congrArg (fun γ : Degree (a + z) s => freePart γ.val) h
  simp only [sourceExponent, corePart_joinParts, freePart_joinParts] at hc hz
  exact congrArg (Sigma.mk i) (Prod.ext (Subtype.ext hc) (Subtype.ext hz))

lemma sourceExponent_surjective (a z s : ℕ) : Function.Surjective (@sourceExponent a z s) := by
  intro β
  let j : Fin (s + 1) := ⟨(corePart β.val).degree, by
    have h := corePart_le_degree β.val
    rw [degree_val] at h
    omega⟩
  let i := (sourceProfileEquiv s).symm j
  have hi : profileSourceIndex i = (corePart β.val).degree := by
    rw [← sourceProfileEquiv_val, Equiv.apply_symm_apply]
  let c : Degree a (profileSourceIndex i) := ⟨corePart β.val, mem_exponents.mpr hi.symm⟩
  let f : Degree z (s - profileSourceIndex i) := ⟨freePart β.val, mem_exponents.mpr (by
    have h := degree_parts β.val
    rw [degree_val] at h
    omega)⟩
  refine ⟨⟨i, c, f⟩, ?_⟩
  apply Subtype.ext
  exact joinParts_parts β.val

def sourceMonomialEquiv (a z s : ℕ) : (Σ i, SourceMonomialFiber a z s i) ≃ Degree (a + z) s :=
  Equiv.ofBijective sourceExponent ⟨sourceExponent_injective a z s, sourceExponent_surjective a z s⟩

/-- Targets of nonzero coarse capacity have at least one free variable. -/
def PositiveTargetMonomial (a z s : ℕ) :=
  {β : Degree (a + z) (2 * s + 1) // (corePart β.val).degree < 2 * s + 1}

instance (a z s : ℕ) : Fintype (PositiveTargetMonomial a z s) := by
  classical
  exact inferInstanceAs (Fintype {β : Degree (a + z) (2 * s + 1) //
    (corePart β.val).degree < 2 * s + 1})

def targetExponent {a z s : ℕ} (β : Σ j, TargetMonomialFiber a z s j) : PositiveTargetMonomial a z s :=
  ⟨⟨joinParts β.2.1.val β.2.2.val, mem_exponents.mpr (by
    rw [degree_joinParts, degree_val, degree_val]
    have hj := β.1.isLt
    omega)⟩, by simpa only [corePart_joinParts, degree_val] using β.1.isLt⟩

lemma targetExponent_injective (a z s : ℕ) : Function.Injective (@targetExponent a z s) := by
  rintro ⟨i, α⟩ ⟨j, β⟩ h
  have hi : i = j := by
    apply Fin.ext
    have hc := congrArg (fun γ : PositiveTargetMonomial a z s => (corePart γ.val.val).degree) h
    simpa only [targetExponent, corePart_joinParts, degree_val] using hc
  subst j
  have hc := congrArg (fun γ : PositiveTargetMonomial a z s => corePart γ.val.val) h
  have hz := congrArg (fun γ : PositiveTargetMonomial a z s => freePart γ.val.val) h
  simp only [targetExponent, corePart_joinParts, freePart_joinParts] at hc hz
  exact congrArg (Sigma.mk i) (Prod.ext (Subtype.ext hc) (Subtype.ext hz))

lemma targetExponent_surjective (a z s : ℕ) : Function.Surjective (@targetExponent a z s) := by
  intro β
  let j : Fin (2 * s + 1) := ⟨(corePart β.val.val).degree, β.property⟩
  let c : Degree a j := ⟨corePart β.val.val, mem_exponents.mpr rfl⟩
  let f : Degree z (2 * s + 1 - j) := ⟨freePart β.val.val, mem_exponents.mpr (by
    have h := degree_parts β.val.val
    rw [degree_val] at h
    dsimp [j]
    omega)⟩
  refine ⟨⟨j, c, f⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact joinParts_parts β.val.val

def targetMonomialEquiv (a z s : ℕ) :
    (Σ j, TargetMonomialFiber a z s j) ≃ PositiveTargetMonomial a z s :=
  Equiv.ofBijective targetExponent ⟨targetExponent_injective a z s, targetExponent_surjective a z s⟩

end Froberg
