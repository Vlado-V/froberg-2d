import Froberg.SparseOutputQuotients

/-! Projected sparse conditions in the very same unrestricted vector
coordinates used by the intermediate-row incidence construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K V I : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n s d m h b : ℕ}

lemma finrank_comap_le_of_injective (L : (Fin h → K) →ₗ[K] V)
    (hL : Function.Injective L) (R : Submodule K V) :
    finrank K (R.comap L)≤finrank K R := by
  let F : R.comap L →ₗ[K] R := (L.comp (R.comap L).subtype).codRestrict R
    (fun x => x.property)
  apply LinearMap.finrank_le_finrank_of_injective (f := F)
  intro x y hxy
  apply Subtype.ext
  apply hL
  exact congrArg Subtype.val hxy

/-- The output-relation open is expressed in the same `Fin m → Fin h → K`
coordinates as the sparse quotient-incidence open, so the two can be
intersected before choosing a single vector tuple. -/
theorem sparse_embedded_relations_open
    (L : (Fin h → K) →ₗ[K] V) (hL : Function.Injective L)
    (R : I → Submodule K V)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {i : Fin m // e i≤β}≤b*β.degree.choose s)
    (hcap : ∀ i,b*(s+d).choose s≤h-finrank K (R i)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → Fin h → K))) K,
      (∃ x,eval x D≠0) ∧
      ∀ v : Fin m → Fin h → K,eval (coordinates K _ v) D≠0 →
        ∀ i c,c≤d → ∀ p : Fin m → Forms K n c,
          (∀ β,sparseOutputCoefficient e (fun j => L (v j)) p β∈R i) → p=0 := by
  let F : I → (Fin h → K) →ₗ[K] (Fin h → K) :=
    fun i => relationProjection ((R i).comap L)
  have hF (i) : b*(s+d).choose s≤finrank K (F i).range := by
    have hrank := (F i).finrank_range_add_finrank_ker
    have hker : (F i).ker=(R i).comap L := relationProjection_kernel _
    rw [hker,Module.finrank_fin_fun] at hrank
    have hdim := finrank_comap_le_of_injective L hL (R i)
    have hc := hcap i
    omega
  obtain ⟨D,hD,hgood⟩ := projected_sparse_injection_open_of_divisor_bound e he b hdiv F hF
  refine ⟨D,hD,?_⟩
  intro v hv i c hc p hp
  have hinj := hgood (coordinates K _ v) hv i c hc
  simp only [LinearEquiv.symm_apply_apply] at hinj
  apply hinj
  rw [map_zero]
  funext j
  apply MvPolynomial.ext
  intro β
  rw [AttachedMultiplication.coefficient_formula]
  have hLcoef : L (sparseOutputCoefficient e v p β)=
      sparseOutputCoefficient e (fun a => L (v a)) p β := by
    simp only [sparseOutputCoefficient,map_sum,map_smul]
  have hmem : sparseOutputCoefficient e v p β∈(R i).comap L := by
    change L (sparseOutputCoefficient e v p β)∈R i
    rw [hLcoef]
    exact hp β
  have hz : F i (sparseOutputCoefficient e v p β)=0 := by
    exact (show (R i).comap L≤(F i).ker from (relationProjection_kernel _).ge) hmem
  simpa only [sparseOutputCoefficient,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Pi.zero_apply,MvPolynomial.coeff_zero,Finsupp.zero_apply] using congrFun hz j

end Froberg
