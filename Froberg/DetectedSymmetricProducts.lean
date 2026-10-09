module

public import Froberg.SymmetricIndependence

@[expose] public section

/-! Detection of independent symmetric products gives the exact separation
condition used by the coefficient map on endpoint homology. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K]
variable {V Z X : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup Z] [Module K Z] [AddCommGroup X] [Module K X]
variable {ι : Type*}

private theorem symProd_mem_span_formalPair (q : ι → V) {a b : V}
    (ha : a ∈ Submodule.span K (Set.range q)) (hb : b ∈ Submodule.span K (Set.range q)) :
    symProd a b ∈ Submodule.span K (Set.range (formalPair (K := K) q)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j,rfl⟩ := hy
      exact Submodule.subset_span ⟨s(i,j),rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      rw [symProd_comm, show symProd (K := K) (b+c) (q i) =
        symProd b (q i) + symProd c (q i) from (symProdLeft (q i)).map_add b c]
      simpa only [symProd_comm] using Submodule.add_mem _ hb hc
    | smul k b _ hb =>
      rw [symProd_comm, show symProd (K := K) (k • b) (q i) =
        k • symProd b (q i) from (symProdLeft (q i)).map_smul k b]
      simpa only [symProd_comm] using Submodule.smul_mem _ k hb
  | zero => simp
  | add a c _ _ ha hc =>
    rw [show symProd (K := K) (a+c) b = symProd a b + symProd c b from
      (symProdLeft b).map_add a c]
    exact Submodule.add_mem _ ha hc
  | smul k a _ ha =>
    rw [show symProd (K := K) (k • a) b = k • symProd a b from
      (symProdLeft b).map_smul k a]
    exact Submodule.smul_mem _ _ ha

theorem formalSquare_span_le_formalPair (q : ι → V) :
    formalSquare (Submodule.span K (Set.range q)) ≤
      Submodule.span K (Set.range (formalPair (K := K) q)) := by
  rintro x ⟨y,rfl⟩
  induction y using symmetricSquare_induction with
  | hprod a b =>
    rw [symmetricMap_symProd]
    exact symProd_mem_span_formalPair q a.2 b.2
  | hzero => simp
  | hadd a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | hsmul k a ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

/-- If a linear detector kills the old product space and detects independent
new unordered products, no nonzero new formal square can be an old product. -/
theorem formalSquare_separated_of_detected_products
    (μ : SymmetricSquare K V →ₗ[K] Z) (T : Z →ₗ[K] X)
    (J : Submodule K Z) (hJ : J ≤ T.ker) (q : ι → V)
    (hq : LinearIndependent K (fun p => T (μ (formalPair (K := K) q p)))) :
    formalSquare (Submodule.span K (Set.range q)) ⊓ J.comap μ = ⊥ := by
  apply le_antisymm
  · rintro x ⟨hx,hxJ⟩
    change x = 0
    have hx' := formalSquare_span_le_formalPair q hx
    rw [← Finsupp.range_linearCombination] at hx'
    obtain ⟨c,hc⟩ := hx'
    have he : T (μ (Finsupp.linearCombination K (formalPair (K := K) q) c)) =
        Finsupp.linearCombination K (fun p => T (μ (formalPair (K := K) q p))) c := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    have hz : Finsupp.linearCombination K (fun p => T (μ (formalPair (K := K) q p))) c = 0 := by
      rw [← he,hc]
      exact hJ hxJ
    have hc0 : c = 0 := hq (hz.trans (map_zero _).symm)
    rw [← hc,hc0,map_zero]
  · exact bot_le

/-- The exact separation hypothesis used in the coefficient injection, with
actual old products as the forbidden subspace. -/
theorem formalSquare_separated_from_mixed_of_detected_products
    (μ : SymmetricSquare K V →ₗ[K] Z) (T : Z →ₗ[K] X)
    (W : Submodule K V) (hW : (formalMixed W).map μ ≤ T.ker) (q : ι → V)
    (hq : LinearIndependent K (fun p => T (μ (formalPair (K := K) q p)))) :
    formalSquare (Submodule.span K (Set.range q)) ⊓
      ((formalMixed W).map μ).comap μ = ⊥ :=
  formalSquare_separated_of_detected_products μ T _ hW q hq

end Froberg
