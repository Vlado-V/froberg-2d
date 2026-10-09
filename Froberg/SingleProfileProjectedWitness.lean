module

public import Froberg.SingleProfileProducts
public import Froberg.GenericDimensions
public import Froberg.SparseIntermediateOpen
public import Froberg.SparseEmbeddedRelations

@[expose] public section

/-! A complete finite B.4 witness from the proved sparse budget and retained
scalar open. The scalar list is chosen once for both conditions. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {n s d R h H m r b j : ℕ}
variable {I : Type*} [Fintype I]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- All parts of a finite even-row witness use the same actual scalar list. -/
theorem exists_single_profile_even_row_with_relations
    (hn : 0<n) (hh : 0<h)
    (w : σ → ℕ) (Yhalf : Finset (Fin n))
    (o : Fin H → MvPolynomial σ K) (ho : LinearIndependent K o)
    (hdegree : ∀ j,(o j).IsHomogeneous R)
    (L : (Fin h → K) →ₗ[K] (Fin H → K)) (hL : Function.Injective L)
    (hLodd : ∀ z,retainMonomials (fun a => Finsupp.weight w a%2=0) (outputCombination o (L z))=0)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s)
    (Relations : I → Submodule K (Fin H → K))
    (hrelations : ∀ i,b*(s+1).choose s≤h-finrank K (Relations i))
    (hcap : b*(s+d).choose s≤h)
    (hcount : h*(s+d).choose s * (r+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
      (h-b*(s+d).choose s)*(n+s+d-1).choose d)
    (P : V →ₗ[K] MvPolynomial (σ ⊕ Fin n) K) (hP : Function.Injective P)
    (hPX : (biformOutputEndomorphism (retainMonomials
      (fun α => Finsupp.weight w α%2=0))).comp P=P)
    (hPY : ∀ p,(P p).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 0) (ProductRows.halfWeight Yhalf)) j)
    (hscalarOpen : ∃ D : MvPolynomial (Fin (finrank K (Fin r → Forms K n d))) K,
      (∃ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0) ∧
      ∀ Q : Fin r → Forms K n d,eval (coordinates K _ Q) D≠0 →
        Function.Injective (ProjectedPrefix.multiplication
          (fun α => MonomialExpansion.partialDegree Yhalf α≠j) Q s)) :
    ∃ (v : Fin m → Fin h → K) (Q : Fin r → Forms K n d),
        (∀ i c,c≤1 → ∀ p : Fin m → Forms K n c,
          (∀ β,sparseOutputCoefficient e (fun k => L (v k)) p β∈Relations i) → p=0) ∧
        (∀ i,(attachedPolynomialFamily o e (fun i => L (v i)) i).IsHomogeneous (R+s)) ∧
        (∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e (fun i => L (v i)) he)) ∧
        (addRow (polynomialIntermediateRow o e (fun i => L (v i)) he Q)
          P).ker =
          ((LinearMap.inl K
            ((Fin r → Fin H → Forms K n s) × (Fin m → Forms K n d))
            V).comp
            (intermediateKoszul e (fun i => L (v i)) he Q)).range := by
  obtain ⟨Dextra,hDextra,hrelationsGood⟩ := sparse_embedded_relations_open (d := 1)
    L hL Relations e he hdiv hrelations
  obtain ⟨v,hvextra,hv,hpos,hinj,D₀,hD₀,hPQ⟩ :=
    exists_sparse_intermediate_in_open hn hh e he hdiv hcap hcount Dextra hDextra
  obtain ⟨D,hD,hDQ⟩ := hscalarOpen
  have hP' : ∃ a,eval a D₀≠0 := by obtain ⟨Q,hQ⟩ := hD₀; exact ⟨coordinates K _ Q,hQ⟩
  have hD' : ∃ a,eval a D≠0 := by obtain ⟨Q,hQ⟩ := hD; exact ⟨coordinates K _ Q,hQ⟩
  obtain ⟨a,haP,haD⟩ := principal_opens_intersect hP' hD'
  let Q : Fin r → Forms K n d := (coordinates K _).symm a
  have hQa : coordinates K _ Q=a := (coordinates K _).apply_symm_apply a
  have hQP : eval (coordinates K _ Q) D₀≠0 := hQa.symm ▸ haP
  have hQD : eval (coordinates K _ Q) D≠0 := hQa.symm ▸ haD
  have hzero : ∀ c≤d,Function.Injective (homogeneousMultiplication (d := c) e (fun i => L (v i)) he) := by
    intro c hc p p' hp
    apply hinj c hc
    have hbase : homogeneousMultiplication (d := c) e v he p=homogeneousMultiplication e v he p' := by
      apply vectorOutputMap_injective L hL
      simpa only [vectorOutputMap_homogeneousMultiplication] using hp
    exact congrArg (fun f j => (f j).val) hbase
  refine ⟨v,Q,hrelationsGood v hvextra,attachedPolynomialFamily_homogeneous o hdegree e _ he,hzero,?_⟩
  exact single_profile_even_row_kernel w Yhalf o ho hdegree L hL hLodd e v he Q
    (hinj d le_rfl) (hPQ Q hQP) P hP hPX hPY (hDQ Q hQD)

end Froberg
