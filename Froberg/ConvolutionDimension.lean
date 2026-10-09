module

public import Froberg.ConvolutionBlocks
public import Froberg.DimensionProjection

@[expose] public section

/-! A prescribed output space needs only the expected number of convolution blocks. -/
noncomputable section
namespace Froberg
open Module
variable {K W : Type*} [Field K] [Infinite K]
  [AddCommMonoid W] [Module K W] [Module.Finite K W]

theorem exists_convolution_blocks_of_dimension {a e m k : ℕ}
    (ha : 0<a) (hm : 0<m) (hdim : finrank K W ≤ k*(a+e-1).choose e) :
    ∃ (o : Fin k × ConvolutionSubset (m+a-1) e → W)
      (f : Fin k × ConvolutionSubset (m+a-1) e → Forms K m e),
      Function.Surjective (vectorFormFamilyMap (t := a-1) o f) := by
  obtain ⟨P, hP⟩ := exists_surjective_linearMap_of_finrank_le
    (V := Fin k → Forms K a e) (W := W) (K := K) (by
      simpa only [Module.finrank_pi_fintype, finrank_forms K a e ha,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hdim)
  exact convolution_blocks_surjective ha hm P hP

def convolutionBlockCount (q a e : ℕ) : ℕ := (q + (a+e-1).choose e - 1) / (a+e-1).choose e

theorem convolutionBlockCount_sufficient (q e : ℕ) {a : ℕ} (ha : 0<a) :
    q ≤ convolutionBlockCount q a e * (a+e-1).choose e := by
  have hp : 0 < (a+e-1).choose e := Nat.choose_pos (by omega)
  have hmod := Nat.mod_lt (q + (a+e-1).choose e - 1) hp
  have hdiv := Nat.mod_add_div (q + (a+e-1).choose e - 1) ((a+e-1).choose e)
  unfold convolutionBlockCount
  rw [Nat.mul_comm]
  omega

/-- The last block may be partial: only the ceiling of the output dimension
by the block output size is required. -/
theorem exists_rounded_convolution_family {a e m : ℕ} (ha : 0<a) (hm : 0<m) :
    ∃ (o : Fin (convolutionBlockCount (finrank K W) a e) ×
        ConvolutionSubset (m+a-1) e → W)
      (f : Fin (convolutionBlockCount (finrank K W) a e) ×
        ConvolutionSubset (m+a-1) e → Forms K m e),
      Function.Surjective (vectorFormFamilyMap (t := a-1) o f) :=
  exists_convolution_blocks_of_dimension ha hm (convolutionBlockCount_sufficient _ _ ha)

end Froberg
