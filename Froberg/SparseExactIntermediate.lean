import Froberg.IntermediateScalar
import Froberg.OuterGeneric

/-! Exact prescribed new-layer counts are obtained by selecting the labels
before choosing the generic vectors. This preserves the full B.11 estimate. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
open Quartic.HomogeneousCoefficientCoordinates
open AttachedMultiplication OuterInjection
variable {K : Type*} [Field K] [Infinite K]

/-- A sparse family of exactly m generators, together with generic injective
scalar action on its true polynomial quotient. -/
theorem exists_exact_sparse_intermediate
    {n s d h b m q : ℕ} (hn : 0<n) (hh : 0<h)
    (hm : m≤b*(n+s-1).choose s) (hcap : b*(s+d).choose s≤h)
    (hcount : h*(s+d).choose s * (q+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
      (h-b*(s+d).choose s)*(n+s+d-1).choose d) :
    ∃ (e : Fin m → Fin n →₀ ℕ) (v : Fin m → Fin h → K),
      ∃ he : ∀ i, (e i).degree=s,
      (∀ β : Fin n →₀ ℕ, Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s) ∧
      (∀ S : Finset (Fin m), S.card≤h → LinearIndependent K (fun i : S => v i.val)) ∧
      MixedExterior.UniversalMixedPosition v ∧
      (∀ c≤d, Function.Injective (AttachedMultiplication.multiplication (d := c) e v)) ∧
      ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
        (∃ Q : Fin q → Forms K n d, eval (coordinates K _ Q) P ≠ 0) ∧
        ∀ Q : Fin q → Forms K n d, eval (coordinates K _ Q) P ≠ 0 →
          Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply (d := d) e v he) Q) := by
  classical
  have hcard : m≤Fintype.card (Labels b n s) := by
    simpa only [Labels,Fintype.card_prod,Fintype.card_fin,Sym.card_sym_eq_choose] using hm
  let f : Fin m ↪ Labels b n s :=
    (⟨Fin.castLE hcard,Fin.castLE_injective hcard⟩ : Fin m ↪ Fin (Fintype.card (Labels b n s))).trans
      (Fintype.equivFin (Labels b n s)).symm.toEmbedding
  let e : Fin m → Fin n →₀ ℕ := fun i => coreExponent 0 (f i)
  have he (i : Fin m) : (e i).degree=s := coreExponent_degree 0 (f i)
  have hdiv (β : Fin n →₀ ℕ) : Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s := by
    let g : {i : Fin m // e i≤β} → {i : Labels b n s // coreExponent 0 i≤β} :=
      fun i => ⟨f i.val,i.property⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact Subtype.ext (f.injective (congrArg Subtype.val hij))
    exact (Fintype.card_le_of_injective g hg).trans (card_target_labels_le 0 β)
  obtain ⟨v,hv,hpos⟩ := MixedExterior.exists_universal_mixed_vectors (K := K) (α := Fin m) h
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
  refine ⟨e,v,he,hdiv,hv,hpos,hinj,?_⟩
  apply intermediate_scalar_injective_of_budget hn hh e v he hv hpos hcap
  · intro β
    have hb := hdiv β.val
    rw [β.property] at hb
    simpa only [labelsBelow,Fintype.card_subtype] using hb
  · exact hcount

end Froberg
