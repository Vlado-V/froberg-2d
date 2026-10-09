module

public import Froberg.CoefficientRowElimination
public import Froberg.MatrixProductKernel

@[expose] public section

/-! Converting exact polynomial rows to the matrix invariant used in the
increasing-degree elimination. Unordered products retain diagonal equations
in every characteristic. -/
noncomputable section
namespace Froberg
open Finset
attribute [local instance] Classical.propDecidable
variable {K : Type} {A I : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype I]

/-- The unordered positive-layer pairs in one total degree. -/
def positiveDegreePair (j : I → ℕ) (r : ℕ) : Sym2 I → Prop :=
  Sym2.lift ⟨fun i k => 0<j i ∧ 0<j k ∧ j i+j k=r,by
    intro i k
    apply propext
    constructor <;> rintro ⟨hi,hk,hik⟩ <;> exact ⟨hk,hi,by omega⟩⟩

@[simp] theorem positiveDegreePair_mk (j : I → ℕ) (r : ℕ) (i k : I) :
    positiveDegreePair j r s(i,k) ↔ 0<j i ∧ 0<j k ∧ j i+j k=r := Iff.rfl

/-- The precise scalar/new-layer exactness and independent formal products
imply the coefficient-row rule required by the induction. -/
theorem coefficientRowExact_of_independent_products
    (V : ℕ → Submodule K A) (a E : I → A) (j : I → ℕ) (r : ℕ)
    (hpairs : LinearIndependent K
      (fun p : {p : Sym2 I // positiveDegreePair j r p} => pairProducts E p.val))
    (hrow : ∀ (u b : I → A) (p : A),
      (∀ i,u i∈V r) → (∀ i,b i∈V 0) →
      p∈Submodule.span K (Set.range
        (fun p : {p : Sym2 I // positiveDegreePair j r p} => pairProducts E p.val)) →
      (∑ i,a i*u i)+(∑ i,if j i=r then E i*b i else 0)+p=0 →
      ∃ C : I → I → K,
        (∀ i k,j k≠r → C i k=0) ∧
        (∀ i,u i=matrixCombination E C i) ∧
        (∀ k,j k=r → b k = -∑ i,C i k • a i) ∧ p=0) :
    CoefficientRowExact V a E j r := by
  classical
  intro u b B hu hb hB hrel
  have hmem : (∑ i,∑ k,B i k • (E i*E k))∈Submodule.span K (Set.range
      (fun p : {p : Sym2 I // positiveDegreePair j r p} => pairProducts E p.val)) := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro k hk
    by_cases hik : 0<j i ∧ 0<j k ∧ j i+j k=r
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨s(i,k),hik⟩,rfl⟩
    · rw [hB i k hik,zero_smul]
      exact Submodule.zero_mem _
  obtain ⟨C,hCs,hCu,hCb,hzero⟩ := hrow u b _ hu hb hmem hrel
  have halt := matrix_product_alternating E (positiveDegreePair j r) hpairs B hB hzero
  refine ⟨C,hCs,hCu,hCb,?_,?_⟩
  · intro i k hi hk hik
    exact halt.1 i k ⟨hi,hk,hik⟩
  · intro i hi hii
    exact halt.2 i ⟨hi,hi,hii⟩

end Froberg
