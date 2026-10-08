import Froberg.Hyperplane
import Froberg.FormalHomology

/-! The exact hyperplane replacement, including its actual endpoint homology interpretation. -/
noncomputable section
namespace Froberg
open Module

variable {K : Type} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Products whose two factors belong to `A` lie in its formal symmetric square. -/
theorem formalProducts_le_formalSquare {Q A : Submodule K V} (hQA : Q ≤ A) :
    formalProducts Q A ≤ formalSquare A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact ⟨symProd (⟨a, hQA ha⟩ : A) (⟨b, hb⟩ : A), symmetricMap_symProd A.subtype _ _⟩

/-- If the relations lie in a coefficient subspace, intersecting formal products is exact. -/
theorem concentrated_formal_relations (R : Submodule K (SymmetricSquare K V))
    (L A : Submodule K V) (h : R ⊓ formalMixed L ≤ formalSquare A) :
    R ⊓ formalMixed L = R ⊓ formalProducts (L ⊓ A) A := by
  calc
    R ⊓ formalMixed L = (R ⊓ formalMixed L) ⊓ formalSquare A := (inf_eq_left.mpr h).symm
    _ = R ⊓ (formalMixed L ⊓ formalSquare A) := inf_assoc _ _ _
    _ = R ⊓ formalProducts (L ⊓ A) A := by rw [formalMixed_inf_formalSquare]

/-- Exact hyperplane replacement for genuine formal symmetric-product relations. -/
theorem formal_hyperplane_replacement (R : Submodule K (SymmetricSquare K V))
    (W A Q Qminus W₀ : Submodule K V) {f M : V} {ε : K}
    (hWA : W ⊓ A = Q) (hQ : Q = Qminus ⊔ Submodule.span K {f})
    (hW : W = W₀ ⊔ Submodule.span K {f}) (hQ₀ : Qminus ≤ W₀)
    (hf₀ : f ∉ W₀) (hM : M ∉ W ⊔ A) (hε : ε ≠ 0)
    (hrelations : R ⊓ formalMixed (W ⊔ Submodule.span K {M}) =
      R ⊓ formalProducts Q A) :
    R ⊓ formalMixed (W₀ ⊔ Submodule.span K {f + ε • M}) =
      R ⊓ formalProducts Qminus A := by
  have h₀W : W₀ ≤ W := by rw [hW]; exact le_sup_left
  have hfW : f ∈ W := by
    rw [hW]
    exact (show Submodule.span K {f} ≤ W₀ ⊔ Submodule.span K {f} from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton f))
  have hinc : W₀ ⊔ Submodule.span K {f + ε • M} ≤ W ⊔ Submodule.span K {M} := by
    apply sup_le (h₀W.trans le_sup_left)
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    apply Submodule.add_mem
    · exact (show W ≤ W ⊔ Submodule.span K {M} from le_sup_left) hfW
    · apply Submodule.smul_mem
      exact (show Submodule.span K {M} ≤ W ⊔ Submodule.span K {M} from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton M))
  have hQA : Q ≤ A := by rw [← hWA]; exact inf_le_right
  have hcon : R ⊓ formalMixed (W₀ ⊔ Submodule.span K {f + ε • M}) ≤ formalSquare A := by
    apply (inf_le_inf le_rfl (formalMixed_mono hinc)).trans
    rw [hrelations]
    exact inf_le_right.trans (formalProducts_le_formalSquare hQA)
  rw [concentrated_formal_relations R _ A hcon,
    hyperplane_replacement_inf W A Q Qminus W₀ hWA hQ hW hQ₀ hf₀ hM hε]

/-- Section 3's replacement interpreted as an equivalence for the actual polynomial
Koszul homology, rather than only an equality of formal subspaces. -/
def endpointHyperplaneReplacement {n d r : ℕ} (htwo : (2 : K) ≠ 0)
    (W A Q Qminus W₀ : Submodule K (Forms K n d))
    {f M : Forms K n d} {ε : K}
    (hWA : W ⊓ A = Q) (hQ : Q = Qminus ⊔ Submodule.span K {f})
    (hW : W = W₀ ⊔ Submodule.span K {f}) (hQ₀ : Qminus ≤ W₀)
    (hf₀ : f ∉ W₀) (hM : M ∉ W ⊔ A) (hε : ε ≠ 0)
    (hrelations :
      (formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
          formalMixed (W ⊔ Submodule.span K {M}) =
        formalPolynomialMultiplication.ker ⊓ formalProducts Q A)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (hspan : Submodule.span K (Set.range q) = W₀ ⊔ Submodule.span K {f + ε • M}) :
    EndpointHomology q ≃ₗ[K]
      ((formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
        formalProducts Qminus A : Submodule K (SymmetricSquare K (Forms K n d))) := by
  have heq :
      (formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
          formalMixed (Submodule.span K (Set.range q)) =
        formalPolynomialMultiplication.ker ⊓ formalProducts Qminus A := by
    rw [hspan]
    exact formal_hyperplane_replacement _ W A Q Qminus W₀ hWA hQ hW hQ₀ hf₀ hM hε hrelations
  exact (endpointHomologyEquivFormal htwo q hq).trans (LinearEquiv.ofEq _ _ heq)

end Froberg
