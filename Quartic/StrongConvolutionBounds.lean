module

public import Quartic.ConvolutionAmbientBounds

@[expose] public section

/-! Uniform image thresholds retain the full quadratic surplus, independently
of the dimensions of the child homology and the subsequent correction space. -/
noncomputable section
namespace Quartic.StrongConvolutionBounds
open Module MvPolynomial ConvolutionFree ConvolutionFreePieces
open ProfileCertificate UniformEndpoint ConvolutionProfileImage
variable {K : Type*} [Field K] [Infinite K]

theorem exists_threshold (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (d : ℕ) (hd : d ≤ totalA m (mixedCount m upper)) :
    ∃ e : ℕ,
      (d : ℝ) * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m upper) : ℝ) - d) ≤ e ∧
      ((UniformScalar.targetCount m (mixedCount m upper) : ℝ) /
          (totalA m (mixedCount m upper) : ℝ) * d +
        (m : ℝ)^2 / 100 * min (d : ℝ) ((totalA m (mixedCount m upper) : ℝ)-d) ≤ e) ∧
      (∀ S : Submodule K (Target K (coreP (mixedCount m upper)+1)
          (freeW m (mixedCount m upper)) 1),
        Submodule.span K (Set.range (GenericF13Endpoint.convolutionMixed K
          (coreP (mixedCount m upper)+1) (freeW m (mixedCount m upper)))) ≤ S →
        finrank K S = d + mixedCount m upper →
        e + mixedCount m upper * (m+1).choose 2 ≤
          finrank K (BilinearImage.image ConvolutionAmbientImage.multiplication S)) := by
  classical
  let t := coreP (mixedCount m upper)+1
  let w := freeW m (mixedCount m upper)
  let V := Piece K t w 1
  have hV : finrank K V = totalA m (mixedCount m upper) :=
    ConvolutionOuterIncidence.endpoint_source_finrank m (by omega) upper
  have hexL : ∃ L : Submodule K V, finrank K L = d := by
    obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := V) (hV ▸ hd)
    exact ⟨Submodule.span K (Set.range v),by rw [finrank_span_eq_card hv,Fintype.card_fin]⟩
  have hex : ∃ e : ℕ, ∃ L : Submodule K V,
      finrank K L = d ∧ finrank K (quadraticImage L) = e := by
    obtain ⟨L,hL⟩ := hexL
    exact ⟨_,L,hL,rfl⟩
  obtain ⟨L,hL,hE⟩ := Nat.find_spec hex
  have hmin : ∀ S : Submodule K V, finrank K S = d →
      Nat.find hex ≤ finrank K (quadraticImage S) := by
    intro S hS
    exact Nat.find_min' hex ⟨S,hS,rfl⟩
  refine ⟨Nat.find hex,?_,?_,?_⟩
  · have h := ConvolutionScalarImages.outer_image_bound m (by omega) upper L
    change (finrank K L : ℝ) * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m upper) : ℝ) - finrank K L) ≤ (finrank K (quadraticImage L) : ℝ) at h
    rw [hL,hE] at h
    exact h
  · have h := ConvolutionProfileBound.uniform_image_surplus m hm upper L
    dsimp only at h
    rw [hL,hE] at h
    exact h
  · have hc := ConvolutionOuterGeneric.endpoint_columns_range m (by omega) upper
    have ht : 2 ≤ t := by dsimp [t]; unfold coreP; omega
    have hcols : t+2 = mixedCount m upper := by dsimp [t]; unfold coreP; omega
    have hvars : t+w = m := ConvolutionOuterGeneric.endpoint_variable_count m (by omega) upper
    have h := (ConvolutionAmbientImage.expansion_iff_ambient ht d (Nat.find hex)).mp hmin
    simpa only [hcols,hvars] using h

end Quartic.StrongConvolutionBounds
