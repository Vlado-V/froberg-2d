module

public import Froberg.PrefixTheorem
public import Froberg.SurjectiveParameterOpen
public import Quartic.BilinearImage

@[expose] public section

/-! The strict-prefix construction gives an independent pure family of the
prescribed dimension that fills the next degree. -/
noncomputable section
namespace Froberg
open Module MvPolynomial Quartic
variable {K : Type*} [Field K] [Infinite K] {n d r : ℕ}

theorem exists_independent_prefix_surjective (hn : 0<n) (hd : 1<d)
    (hlarge : (1+d).choose 1*((1+d).choose 1*d.choose 1)≤n)
    (hr : (n+(d+1)-1).choose (d+1)≤r*n)
    (hrdim : r≤(n+d-1).choose d) :
    ∃ q : Fin r → Forms K n d,LinearIndependent K q ∧
      Function.Surjective (prefixMultiplication q 1) := by
  classical
  obtain ⟨q,hq⟩ := exists_prefix_surjective_of_large_variables (K := K) hn hd hlarge
    (by simpa using hr)
  let a₀ := coefficientCoordinates q
  have ha₀ : coefficientForms K n d r a₀=q := coefficientCoordinates.symm_apply_apply q
  obtain ⟨D,hD,hgood⟩ := surjective_polynomial_principal_open
    (coefficientPrefixMultiplication (K := K) (n := n) (d := d) (r := r) 1)
    (isPolynomialFamily_linear _) a₀ (by change Function.Surjective (prefixMultiplication _ 1); rwa [ha₀])
  obtain ⟨E,hE,hind⟩ := coefficient_independence_principal_open (K := K) hn hrdim
  obtain ⟨a,haD,haE⟩ := principal_opens_intersect ⟨a₀,hD⟩ hE
  exact ⟨coefficientForms K n d r a,hind a haE,hgood a haD⟩

theorem exists_pure_cutoff_subspace (hn : 0<n) (hd : 1<d)
    (hlarge : (1+d).choose 1*((1+d).choose 1*d.choose 1)≤n)
    (hr : (n+(d+1)-1).choose (d+1)≤r*n)
    (hrdim : r≤(n+d-1).choose d) :
    ∃ U : Submodule K (Forms K n d),finrank K U=r ∧
      BilinearImage.image (gradedMultiplication (K := K) (n := n) (d := d) (e := 1)).flip U=⊤ := by
  obtain ⟨q,hq,hfill⟩ := exists_independent_prefix_surjective (K := K) hn hd hlarge hr hrdim
  refine ⟨Submodule.span K (Set.range q),?_,?_⟩
  · simpa using finrank_span_eq_card hq
  · rw [← BilinearImage.range_tupleMap]
    exact LinearMap.range_eq_top.mpr hfill

end Froberg
