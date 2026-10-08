import Froberg.AttachedProjection

/-! The exceptional-projection bound for arbitrary multiplier degree.
This is the geometric input to the intermediate-layer shadow estimate B.11. -/
noncomputable section
namespace Froberg.MonomialExpansion

/-- Multiples of one monomial with a degree excess have only degree-(d-1)
many remaining parameters in total degree s+d. -/
theorem card_targets_above_general {n s d : ℕ} (hn : 0 < n) (p : Fin n →₀ ℕ)
    (hp : s+1 ≤ p.degree) (T : Finset (Fin n →₀ ℕ))
    (hT : ∀ b ∈ T, b.degree = s+d ∧ p ≤ b) :
    T.card ≤ (n+(d-1)-1).choose (d-1) := by
  classical
  let r := s+d-p.degree
  have hr : r ≤ d-1 := by omega
  have hmap : T.image (fun b => b-p) ⊆ exponents n r := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hbd,hpb⟩ := hT b hb
    have hh := congrArg Finsupp.degree (add_tsub_cancel_of_le hpb)
    rw [map_add,hbd] at hh
    apply mem_exponents.mpr
    dsimp [r]
    omega
  have hi : Set.InjOn (fun b : Fin n →₀ ℕ => b-p) T := by
    intro a ha b hb he
    have ha' := add_tsub_cancel_of_le (hT a ha).2
    have hb' := add_tsub_cancel_of_le (hT b hb).2
    exact ha'.symm.trans ((congrArg (fun c => p+c) he).trans hb')
  calc
    T.card = (T.image (fun b => b-p)).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ (exponents n r).card := Finset.card_le_card hmap
    _ = (n+r-1).choose r := card_exponents n r
    _ ≤ (n+(d-1)-1).choose (d-1) := by
      rw [← Nat.choose_symm (by omega : r ≤ n+r-1),
        ← Nat.choose_symm (by omega : d-1 ≤ n+(d-1)-1)]
      have he1 : n+r-1-r = n-1 := by omega
      have he2 : n+(d-1)-1-(d-1) = n-1 := by omega
      rw [he1,he2]
      exact Nat.choose_le_choose (n-1) (by omega)

/-- Distinct equal-degree monomials have at most N_(d-1)(n) common targets. -/
theorem card_common_targets_general {n s d : ℕ} (hn : 0 < n) (a b : Fin n →₀ ℕ)
    (ha : a.degree = s) (hb : b.degree = s) (hne : a ≠ b)
    (T : Finset (Fin n →₀ ℕ))
    (hT : ∀ c ∈ T, c.degree = s+d ∧ a ≤ c ∧ b ≤ c) :
    T.card ≤ (n+(d-1)-1).choose (d-1) :=
  card_targets_above_general hn (a ⊔ b) (degree_sup_ge_succ ha hb hne) T
    (fun c hc => ⟨(hT c hc).1,sup_le (hT c hc).2.1 (hT c hc).2.2⟩)

end Froberg.MonomialExpansion
namespace Froberg.MixedExterior
open Module
variable {K α : Type*} [Field K] [DecidableEq α]

theorem card_targets_hit_by_labels_general {n s d : ℕ} (hn : 0 < n)
    (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (e : α → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s)
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = s+d ∧ a ≤ b)
    (L : Finset α) (hit : ∀ b ∈ E, ∃ i ∈ L, e i ≠ a ∧ e i ≤ b) :
    E.card ≤ L.card * (n+(d-1)-1).choose (d-1) := by
  classical
  let targets : α → Finset (Fin n →₀ ℕ) := fun i => E.filter (fun b => e i ≠ a ∧ e i ≤ b)
  have hsub : E ⊆ L.biUnion targets := by
    intro b hb
    obtain ⟨i,hi,hia,hib⟩ := hit b hb
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hb,hia,hib⟩⟩
  have hcard : ∀ i ∈ L, (targets i).card ≤ (n+(d-1)-1).choose (d-1) := by
    intro i _
    by_cases hi : e i = a
    · simp [targets,hi]
    · apply MonomialExpansion.card_common_targets_general hn a (e i) ha (he i) (Ne.symm hi)
      intro b hb
      obtain ⟨hb,hne,hib⟩ := Finset.mem_filter.mp hb
      exact ⟨(hE b hb).1,(hE b hb).2,hib⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul L targets _ hcard)

theorem card_deficient_targets_general {n s d h : ℕ} (hn : 0 < n)
    (v : α → Fin h → K) (hv : UniversalMixedPosition v)
    (U : Submodule K (Fin h → K)) (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (e : α → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s)
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = s+d ∧ a ≤ b)
    (sets : (Fin n →₀ ℕ) → Finset α)
    (hsets : ∀ b ∈ E, ∀ i ∈ sets b, e i ≠ a ∧ e i ≤ b)
    (hsize : ∀ b ∈ E, (sets b).card ≤ h)
    (hfail : ∀ b ∈ E, finrank K ↥(U ⊔ blockSpan v (sets b)) <
      min (finrank K U + (sets b).card) h) :
    E.card ≤ (h*2^h) * (n+(d-1)-1).choose (d-1) := by
  obtain ⟨L,hL,hits⟩ := exists_deficient_hitting_set v hv U sets E hsize hfail
  have hc := card_targets_hit_by_labels_general hn a ha e he E hE L (by
    intro b hb
    obtain ⟨i,hi,hib⟩ := hits b hb
    exact ⟨i,hi,hsets b hb i hib⟩)
  exact hc.trans (Nat.mul_le_mul_right _ hL)
end Froberg.MixedExterior
namespace Froberg.AttachedMultiplication
open Module MixedExterior
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n h s d : ℕ}

theorem card_deficient_fiber_projections_general (hn : 0 < n)
    (e : I → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s) (v : I → Fin h → K)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : UniversalMixedPosition v) (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (U : Submodule K (Fin h → K)) (hU : relationFiber e v a ≤ U)
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = s+d ∧ a ≤ b)
    (hsize : ∀ b ∈ E, (labelsBelow e b).card ≤ h)
    (hf : ∀ b ∈ E, finrank K (U.map (relationFiber e v b).mkQ) <
      min (finrank K (U.map (relationFiber e v a).mkQ))
        (finrank K ((Fin h → K) ⧸ relationFiber e v b))) :
    E.card ≤ (h*2^h) * (n+(d-1)-1).choose (d-1) := by
  apply card_deficient_targets_general hn v hm U a ha e he E hE
    (fun b => labelsBelow e b \ labelsBelow e a)
  · intro b hb i hi
    obtain ⟨hib,hia⟩ := Finset.mem_sdiff.mp hi
    refine ⟨?_,(mem_labelsBelow e b i).mp hib⟩
    intro hei
    exact hia ((mem_labelsBelow e a i).mpr (hei ▸ le_rfl))
  · intro b hb
    exact (Finset.card_le_card Finset.sdiff_subset).trans (hsize b hb)
  · intro b hb
    have hST := labelsBelow_mono e (hE b hb).2
    apply deficient_block_projection hST
      (hv _ ((Finset.card_le_card hST).trans (hsize b hb))) (hv _ (hsize b hb)) U
    · rw [← relationFiber_eq_blockSpan e v a]
      exact hU
    · have hh := hf b hb
      rw [relationFiber_eq_blockSpan e v a,relationFiber_eq_blockSpan e v b] at hh
      exact hh

/-- Uniform exceptional projections for any actual source-quotient subspace,
with arbitrary positive or zero multiplier degree d. -/
theorem card_deficient_quotient_projections_general (hn : 0 < n)
    (e : I → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s) (v : I → Fin h → K)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : UniversalMixedPosition v) (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (L : Submodule K ((Fin h → K) ⧸ relationFiber e v a))
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = s+d ∧ a ≤ b)
    (hsize : ∀ b ∈ E, (labelsBelow e b).card ≤ h)
    (hf : ∀ b (hb : b ∈ E), finrank K (L.map (fiberProjection e v (hE b hb).2)) <
      min (finrank K L) (finrank K ((Fin h → K) ⧸ relationFiber e v b))) :
    E.card ≤ (h*2^h) * (n+(d-1)-1).choose (d-1) := by
  let U := L.comap (relationFiber e v a).mkQ
  have hsource : U.map (relationFiber e v a).mkQ = L :=
    Submodule.map_comap_eq_of_surjective (relationFiber e v a).mkQ_surjective L
  apply card_deficient_fiber_projections_general hn e he v hv hm a ha U
    (Quartic.QuotientBilinearImage.le_preimage _ L) E hE hsize
  intro b hb
  have htarget : U.map (relationFiber e v b).mkQ =
      L.map (fiberProjection e v (hE b hb).2) := by
    calc
      _ = (U.map (relationFiber e v a).mkQ).map
          (fiberProjection e v (hE b hb).2) := by
        rw [← Submodule.map_comp,fiberProjection,Submodule.factor_comp_mk]
      _ = _ := by rw [hsource]
  rw [hsource,htarget]
  exact hf b hb
end Froberg.AttachedMultiplication
