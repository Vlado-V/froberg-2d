module

public import Froberg.ProductRowPairs
public import Froberg.CoefficientRowFromPairs

@[expose] public section

/-! Product-row columns remain independent after scalar labels and a common
generator enumeration are added. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] {I σ : Type*}

/-- Enumerating the positive layers gives exactly the positive unordered
pairs, even when the ambient list also has scalar generator labels. -/
def positivePairEquiv {J : Finset ℕ} {counts : ℕ → ℕ}
    (degree : I → ℕ) (ι : LayerLabel J counts → I)
    (hι : Function.Injective ι) (hdegree : ∀ a,degree (ι a)=a.1.val)
    (hpositive : ∀ j∈J,0<j)
    (hcover : ∀ i,0<degree i → ∃ a,ι a=i) (R : ℕ) :
    {p : Sym2 (LayerLabel J counts) // pairDegree p=R} ≃
      {p : Sym2 I // positiveDegreePair degree R p} := by
  let f : {p : Sym2 (LayerLabel J counts) // pairDegree p=R} →
      {p : Sym2 I // positiveDegreePair degree R p} := fun p =>
    ⟨Sym2.map ι p.val,by
      rcases p with ⟨p,hp⟩
      induction p using Sym2.inductionOn with
      | _ a b =>
        change 0<degree (ι a) ∧ 0<degree (ι b) ∧ degree (ι a)+degree (ι b)=R
        rw [hdegree,hdegree]
        exact ⟨hpositive _ a.1.property,hpositive _ b.1.property,hp⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    exact Sym2.map.injective hι (congrArg Subtype.val hab)
  · rintro ⟨p,hp⟩
    induction p using Sym2.inductionOn with
    | _ i k =>
      change 0<degree i ∧ 0<degree k ∧ degree i+degree k=R at hp
      obtain ⟨a,rfl⟩ := hcover i hp.1
      obtain ⟨b,rfl⟩ := hcover k hp.2.1
      refine ⟨⟨s(a,b),?_⟩,?_⟩
      · change a.1.val+b.1.val=R
        simpa only [hdegree] using hp.2.2
      · rfl

/-- An injective polynomial product row gives independence of all positive
unordered products in the common generator enumeration. -/
theorem prepared_pair_independence {J : Finset ℕ} {counts : ℕ → ℕ}
    (q : (j : ℕ) → Fin (counts j) → MvPolynomial σ K)
    (degree : I → ℕ) (ι : LayerLabel J counts → I)
    (hι : Function.Injective ι) (hdegree : ∀ a,degree (ι a)=a.1.val)
    (hpositive : ∀ j∈J,0<j)
    (hcover : ∀ i,0<degree i → ∃ a,ι a=i)
    (E : I → MvPolynomial σ K) (hE : ∀ a,E (ι a)=q a.1.val a.2)
    (R : ℕ) (hq : Function.Injective (multiplication counts q J R)) :
    LinearIndependent K (fun p : {p : Sym2 I // positiveDegreePair degree R p} =>
      pairProducts E p.val) := by
  let e := positivePairEquiv degree ι hι hdegree hpositive hcover R
  have h := (linearIndependent_degree_pairs counts R q hq).comp e.symm e.symm.injective
  convert h using 1
  funext p
  change pairProducts E p.val=pairProducts (fun a : LayerLabel J counts => q a.1.val a.2) (e.symm p).val
  have he := congrArg Subtype.val (e.apply_symm_apply p)
  change Sym2.map ι (e.symm p).val=p.val at he
  rw [← he]
  generalize (e.symm p).val=a
  induction a using Sym2.inductionOn with
  | _ i k => simp only [Sym2.map_mk,pairProducts_mk,hE,Function.comp_apply]

/-- Every positive product belongs to the actual product-row image. -/
theorem prepared_pair_mem_product_range {J : Finset ℕ} {counts : ℕ → ℕ}
    (q : (j : ℕ) → Fin (counts j) → MvPolynomial σ K)
    (degree : I → ℕ) (ι : LayerLabel J counts → I)
    (hι : Function.Injective ι) (hdegree : ∀ a,degree (ι a)=a.1.val)
    (hpositive : ∀ j∈J,0<j)
    (hcover : ∀ i,0<degree i → ∃ a,ι a=i)
    (E : I → MvPolynomial σ K) (hE : ∀ a,E (ι a)=q a.1.val a.2)
    (R : ℕ) (p : {p : Sym2 I // positiveDegreePair degree R p}) :
    pairProducts E p.val∈(multiplication counts q J R).range := by
  classical
  let e := positivePairEquiv degree ι hι hdegree hpositive hcover R
  obtain ⟨a,ha⟩ := exists_rowPair counts (e.symm p).val (e.symm p).property
  refine ⟨Finsupp.single a 1,?_⟩
  change Finsupp.linearCombination K (fun a => products counts q a.1 a.2) (Finsupp.single a 1)=_
  rw [Finsupp.linearCombination_single,one_smul,products_eq_pairProducts,ha]
  have he := congrArg Subtype.val (e.apply_symm_apply p)
  change Sym2.map ι (e.symm p).val=p.val at he
  rw [← he]
  generalize (e.symm p).val=b
  induction b using Sym2.inductionOn with
  | _ i k => simp only [Sym2.map_mk,pairProducts_mk,hE]

end Froberg.ProductRows
