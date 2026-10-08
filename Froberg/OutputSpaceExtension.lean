import Froberg.PrefixConvolution
import Quartic.SplitMiddle22

/-! Successful output families can be placed inside a subspace of any larger
permitted dimension; the convolution generators remain inside that subspace. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K] [Infinite K]
variable {h m j e x y q r D : ℕ}

theorem exists_biform_family_in_extended_output_space
    (hh : 0 < h) (hm : 0 < m) (Q : Fin q → Forms K h j)
    (hQ : Function.Surjective (prefixMultiplication Q x))
    (hqD : q ≤ D) (hD : D ≤ (h+j-1).choose j)
    (hr : convolutionBlockCount q (y+1) e*(m+(y+1)+e-2).choose e ≤ r) :
    ∃ (W : Submodule K (Forms K h j)) (o : Fin r → W)
      (f : Fin r → Forms K m e), finrank K W = D ∧
      Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => (o i).val) f) := by
  have hq : finrank K (Submodule.span K (Set.range Q)) ≤ D := by
    have hcard : finrank K (Submodule.span K (Set.range Q)) ≤ q := by
      simpa only [Fintype.card_fin,Set.finrank] using finrank_range_le_card (R := K) Q
    exact hcard.trans hqD
  obtain ⟨W,hW,hWD⟩ := Quartic.SplitMiddle22.exists_extension_finrank
    (Submodule.span K (Set.range Q)) D hq (by rwa [finrank_forms K h j hh])
  obtain ⟨o,f,ho,hf⟩ := exists_biform_family_of_prefix (y := y) hm Q hQ hr
  exact ⟨W,fun i => ⟨o i,hW (ho i)⟩,f,hWD,hf⟩

end Froberg
