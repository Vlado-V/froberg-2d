module

public import Froberg.ExceptionalTargetCount
public import Froberg.BlockProjection
public import Froberg.AttachedFibers

@[expose] public section

/-! Uniform exceptional projection bounds in the genuine monomial quotient fibers. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MixedExterior
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n h : ℕ}

/-- Labels of attached monomials dividing a given monomial. -/
def labelsBelow (e : I → Fin n →₀ ℕ) (b : Fin n →₀ ℕ) : Finset I :=
  Finset.univ.filter (fun i => e i ≤ b)

@[simp] theorem mem_labelsBelow (e : I → Fin n →₀ ℕ) (b : Fin n →₀ ℕ) (i : I) :
    i ∈ labelsBelow e b ↔ e i ≤ b := by simp [labelsBelow]

theorem labelsBelow_mono (e : I → Fin n →₀ ℕ) {a b : Fin n →₀ ℕ} (hab : a ≤ b) :
    labelsBelow e a ⊆ labelsBelow e b := by
  intro i hi
  exact (mem_labelsBelow e b i).mpr (((mem_labelsBelow e a i).mp hi).trans hab)

theorem relationFiber_eq_blockSpan (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (b : Fin n →₀ ℕ) : relationFiber e v b = blockSpan v (labelsBelow e b) := by
  unfold relationFiber blockSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,(mem_labelsBelow e b i.val).mpr i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,(mem_labelsBelow e b i).mp hi⟩,rfl⟩

theorem relationFiber_mono (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    {a b : Fin n →₀ ℕ} (hab : a ≤ b) : relationFiber e v a ≤ relationFiber e v b := by
  rw [relationFiber_eq_blockSpan,relationFiber_eq_blockSpan]
  exact blockSpan_mono v (labelsBelow_mono e hab)

/-- The genuine quotient projection from a source monomial fiber to a divisible
higher-degree monomial fiber. -/
def fiberProjection (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    {a b : Fin n →₀ ℕ} (hab : a ≤ b) :
    ((Fin h → K) ⧸ relationFiber e v a) →ₗ[K]
      ((Fin h → K) ⧸ relationFiber e v b) :=
  Submodule.factor (relationFiber_mono e v hab)

/-- For one source monomial, the number of deficient actual fiber projections
is uniformly `O(m^s)` for every source subspace. The relation vectors remain
attached to their prescribed monomials throughout the argument. -/
theorem card_deficient_fiber_projections_le {s : ℕ} (hn : 0 < n)
    (e : I → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s)
    (v : I → Fin h → K)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : UniversalMixedPosition v)
    (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (U : Submodule K (Fin h → K)) (hU : relationFiber e v a ≤ U)
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = 2*s+1 ∧ a ≤ b)
    (hsize : ∀ b ∈ E, (labelsBelow e b).card ≤ h)
    (hf : ∀ b ∈ E, finrank K (U.map (relationFiber e v b).mkQ) <
      min (finrank K (U.map (relationFiber e v a).mkQ))
        (finrank K ((Fin h → K) ⧸ relationFiber e v b))) :
    E.card ≤ (h*2^h) * (n+s-1).choose s := by
  apply card_deficient_targets_le hn v hm U a ha e he E hE
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

/-- The same uniform bound stated directly for arbitrary subspaces of the actual
source quotient, with the actual canonical quotient projections. -/
theorem card_deficient_quotient_projections_le {s : ℕ} (hn : 0 < n)
    (e : I → Fin n →₀ ℕ) (he : ∀ i, (e i).degree = s)
    (v : I → Fin h → K)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : UniversalMixedPosition v)
    (a : Fin n →₀ ℕ) (ha : a.degree = s)
    (L : Submodule K ((Fin h → K) ⧸ relationFiber e v a))
    (E : Finset (Fin n →₀ ℕ)) (hE : ∀ b ∈ E, b.degree = 2*s+1 ∧ a ≤ b)
    (hsize : ∀ b ∈ E, (labelsBelow e b).card ≤ h)
    (hf : ∀ b (hb : b ∈ E), finrank K (L.map (fiberProjection e v (hE b hb).2)) <
      min (finrank K L) (finrank K ((Fin h → K) ⧸ relationFiber e v b))) :
    E.card ≤ (h*2^h) * (n+s-1).choose s := by
  let U := L.comap (relationFiber e v a).mkQ
  have hsource : U.map (relationFiber e v a).mkQ = L := by
    exact Submodule.map_comap_eq_of_surjective (relationFiber e v a).mkQ_surjective L
  apply card_deficient_fiber_projections_le hn e he v hv hm a ha U
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
