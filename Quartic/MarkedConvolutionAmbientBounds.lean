module

public import Quartic.ConvolutionAmbientImage
public import Quartic.MarkedFiniteBounds

@[expose] public section

/-!
# Geometric witness thresholds for all convolution subspaces

For each source dimension, the least actual image dimension is attained.
It satisfies the proved scalar inequalities and gives the equivalent fixed
ambient expansion bound. This construction works over any infinite field,
including the algebraic closure used by the projective openness argument.
-/
noncomputable section
namespace Quartic.MarkedConvolutionAmbientBounds
open Module MvPolynomial ConvolutionFree ConvolutionFreePieces
open ProfileCertificate UniformEndpoint ConvolutionProfileImage
variable {K : Type*} [Field K] [Infinite K]

/-- An attained integer image threshold at every source dimension, carrying
both incidence inequalities and the actual ambient all-planes bound. -/
theorem exists_threshold (m : ℕ) (hm : 41 ≤ m) (hmhi : m ≤ 319)
    (hpositive : 0 < Counts.chi (m + 3) (upperEndpoint m + mixedCount m false + 4))
    (d : ℕ) (hd : d ≤ totalA m (mixedCount m false)) :
    ∃ e : ℕ,
      (d : ℝ) * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m false) : ℝ) - d) ≤ e ∧
      (0 < d → d < totalA m (mixedCount m false) →
        SharpMinimization.ImageBoundsReal
          (HullCertificate.markedScalars (HullCertificate.scalars m (upperEndpoint m) (mixedCount m false))) (e : ℝ) d) ∧
      (∀ S : Submodule K (Target K (coreP (mixedCount m false)+1)
          (freeW m (mixedCount m false)) 1),
        Submodule.span K (Set.range (GenericF13Endpoint.convolutionMixed K
          (coreP (mixedCount m false)+1) (freeW m (mixedCount m false)))) ≤ S →
        finrank K S = d + mixedCount m false →
        e + mixedCount m false * (m+1).choose 2 ≤
          finrank K (BilinearImage.image ConvolutionAmbientImage.multiplication S)) := by
  classical
  let t := coreP (mixedCount m false)+1
  let w := freeW m (mixedCount m false)
  let V := Piece K t w 1
  have hV : finrank K V = totalA m (mixedCount m false) :=
    ConvolutionOuterIncidence.endpoint_source_finrank m hm false
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
  · have h := ConvolutionScalarImages.outer_image_bound m hm false L
    change (finrank K L : ℝ) * ((upperEndpoint m : ℝ) + (totalA m (mixedCount m false) : ℝ) - finrank K L) ≤ (finrank K (quadraticImage L) : ℝ) at h
    rw [hL,hE] at h
    exact h
  · intro hpos hlt
    obtain ⟨i,n₁,n₂,n₃,hi,hn₃,hn₂,hn₁,hd,himage,_⟩ :=
      ConvolutionProfileBound.exists_profile_bounds m (mixedCount m false)
        (ConvolutionFiniteImages.canonical_mixedCount_ge_four m (by omega) hmhi false) L
    have hd' : finrank K L = ProfileCertificate.profileDim i n₁ n₂ n₃ := hd
    have hb := MarkedFiniteBounds.source_scalar_inequalities m hm hmhi hpositive
      i n₁ n₂ n₃ hi hn₁ hn₂ hn₃ (by omega) (by omega)
    rw [←hd'] at hb
    have hh := hb.mono himage
    rw [hL,hE] at hh
    exact hh
  · have hc := ConvolutionOuterGeneric.endpoint_columns_range m hm false
    have ht : 2 ≤ t := by dsimp [t]; unfold coreP; omega
    have hcols : t+2 = mixedCount m false := by dsimp [t]; unfold coreP; omega
    have hvars : t+w = m := ConvolutionOuterGeneric.endpoint_variable_count m hm false
    have h := (ConvolutionAmbientImage.expansion_iff_ambient ht d (Nat.find hex)).mp hmin
    simpa only [hcols,hvars] using h

end Quartic.MarkedConvolutionAmbientBounds
