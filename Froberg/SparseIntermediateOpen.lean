module

public import Froberg.SparseExactIntermediate
public import Froberg.UniversalMixedCoordinates

@[expose] public section

/-! The sparse quotient witness is compatible with every prescribed nonempty
open on its actual output vectors, while keeping the exponents fixed. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
open AttachedMultiplication
variable {K : Type*} [Field K] [Infinite K]

theorem exists_sparse_intermediate_in_open
    {n s d h b m q : ℕ} (hn : 0<n) (hh : 0<h)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s)
    (hcap : b*(s+d).choose s≤h)
    (hcount : h*(s+d).choose s * (q+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
      (h-b*(s+d).choose s)*(n+s+d-1).choose d)
    (D : MvPolynomial (Fin (finrank K (Fin m → Fin h → K))) K)
    (hD : ∃ x,eval x D≠0) :
    ∃ v : Fin m → Fin h → K,
      eval (coordinates K _ v) D≠0 ∧
      (∀ S : Finset (Fin m),S.card≤h → LinearIndependent K (fun i : S => v i.val)) ∧
      MixedExterior.UniversalMixedPosition v ∧
      (∀ c≤d,Function.Injective (AttachedMultiplication.multiplication (d := c) e v)) ∧
      ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
        (∃ Q : Fin q → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin q → Forms K n d,eval (coordinates K _ Q) P≠0 →
          Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply (d := d) e v he) Q) := by
  classical
  obtain ⟨v,hvD,hv,hpos⟩ := MixedExterior.exists_universal_mixed_vectors_in_open h D hD
  have hinj (c : ℕ) (hc : c≤d) : Function.Injective
      (AttachedMultiplication.multiplication (d := c) e v) := by
    apply injective_of_independent_fibers e v he
    intro β hβ
    let S : Finset (Fin m) := Finset.univ.filter (fun i => e i≤β)
    have hS : S.card≤h := by
      have hb := hdiv β
      rw [hβ] at hb
      have hc' := (Nat.mul_le_mul_left b
        (Nat.choose_le_choose s (Nat.add_le_add_left hc s))).trans hcap
      have hcardS : S.card=Fintype.card {i : Fin m // e i≤β} := by
        simp only [S,Fintype.card_subtype]
      omega
    let g : {i : Fin m // e i≤β} → S := fun i =>
      ⟨i.val,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using i.property⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact Subtype.ext (congrArg (fun x : S => x.val) hij)
    exact (hv S hS).comp g hg
  refine ⟨v,hvD,hv,hpos,hinj,?_⟩
  apply intermediate_scalar_injective_of_budget hn hh e v he hv hpos hcap
  · intro β
    have hb := hdiv β.val
    rw [β.property] at hb
    simpa only [labelsBelow,Fintype.card_subtype] using hb
  · exact hcount

end Froberg
