module

public import Froberg.Generic
public import Froberg.Prefix
public import Froberg.MonomialCounts

@[expose] public section

/-! Actual surjective multiplication families obtained from a proved endpoint. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K] {n d r : ℕ}

theorem exists_prefix_surjective_of_endpoint (hn : 0 < n)
    (hgen : GenericEndpoint K n d r) (he : euler n d r ≤ 0) :
    ∃ q : Fin r → Forms K n d, LinearIndependent K q ∧
      Function.Surjective (prefixMultiplication q d) := by
  obtain ⟨D,⟨a,ha⟩,hD⟩ := hgen
  obtain ⟨hlin,hdim⟩ := hD a ha
  let q := coefficientForms K n d r a
  have hzero : finrank K (EndpointQuotient K n d (coefficientSpace K n d r a)) = 0 := by
    rw [endpoint_finrank_eq_hilbertFunction _ (coefficientSpace_homogeneous K n d r a),hdim]
    exact Int.toNat_eq_zero.mpr he
  have hrank := endpoint_quotient_add_rank hn q
  change finrank K (EndpointQuotient K n d (coefficientSpace K n d r a)) + _ = _ at hrank
  rw [hzero,zero_add,← finrank_forms K n (2*d) hn] at hrank
  have hsurj : Function.Surjective (endpointMultiplication q) := by
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq hrank
  refine ⟨q,hlin,?_⟩
  intro z
  let z' : Forms K n (2*d) := ⟨z.val, by simpa only [two_mul] using z.property⟩
  obtain ⟨c,hc⟩ := hsurj z'
  refine ⟨c,Subtype.ext ?_⟩
  simpa only [prefixMultiplication_val,endpointMultiplication_val] using congrArg Subtype.val hc

theorem exists_prefix_surjective_at_upperCount (hn : 0 < n)
    (hgen : GenericEndpoint K n d (upperCount n d)) :
    ∃ q : Fin (upperCount n d) → Forms K n d, LinearIndependent K q ∧
      Function.Surjective (prefixMultiplication q d) :=
  exists_prefix_surjective_of_endpoint hn hgen (euler_upperCount_nonpos hn d)

end Froberg
