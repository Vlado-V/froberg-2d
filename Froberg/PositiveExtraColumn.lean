module

public import Froberg.ComponentQuotientIndependence
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Separating the temporary extra positive column from the retained
positive family preserves their joint independence in the scalar quotient. -/
noncomputable section
namespace Froberg
variable {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem independent_extra_reindex (g : J → V) (hg : LinearIndependent K g)
    (M : J) (b : I → J) (hb : Function.Injective b) (hM : ∀ i,b i≠M) :
    LinearIndependent K (fun i : Option I => i.elim (g M) (fun j => g (b j))) := by
  let f : Option I → J := fun i => i.elim M b
  have hf : Function.Injective f := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (hM j hij.symm).elim
    | some i =>
      cases j with
      | none => exact (hM i hij).elim
      | some j => exact congrArg some (hb hij)
  have hi := hg.comp f hf
  convert hi using 1
  funext i
  cases i <;> rfl

theorem quotient_extra_even_column {e u : ℕ}
    (A : Submodule K V) (E : Fin (e+1) → V) (G : Fin u → V)
    (h : LinearIndependent K (fun i : Fin (e+1) ⊕ Fin u => A.mkQ (Sum.elim E G i)))
    (M : Fin (e+1)) :
    LinearIndependent K (fun i : Option (Fin e ⊕ Fin u) =>
      A.mkQ (i.elim (E M) (Sum.elim (fun j => E (M.succAbove j)) G))) := by
  let b : Fin e ⊕ Fin u → Fin (e+1) ⊕ Fin u := Sum.map M.succAbove id
  have hb : Function.Injective b :=
    Function.Injective.sumMap (Fin.succAbove_right_injective) Function.injective_id
  have hM : ∀ i,b i≠Sum.inl M := by
    intro i
    cases i with
    | inl j => exact fun he => Fin.succAbove_ne M j (Sum.inl.inj he)
    | inr j =>
      intro he
      change Sum.inr j=Sum.inl M at he
      cases he
  have hi := independent_extra_reindex _ h (Sum.inl M) b hb hM
  convert hi using 1
  funext i
  cases i with
  | none => rfl
  | some i => cases i <;> rfl

end Froberg
