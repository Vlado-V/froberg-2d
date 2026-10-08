import Quartic.QuotientBilinearImage
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-! Actual failure of a quotient projection forces vanishing exterior products. -/
noncomputable section
namespace Froberg.ProjectionFailure
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The image of a subspace under projection is measured by its sum with the kernel. -/
theorem image_finrank_add (U T : Submodule K V) :
    finrank K (U.map T.mkQ) + finrank K T = finrank K ↥(U ⊔ T) := by
  have h := Quartic.QuotientBilinearImage.finrank_map_mkQ_add T (U ⊔ T) le_sup_right
  have hmap : (U ⊔ T).map T.mkQ = U.map T.mkQ := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  rw [hmap] at h
  exact h

/-- This is the precise rank-failure implication for the outer quotient: adding
`k` independent relations to the base makes a projection deficient only if the
lifted subspace and these added relations fail their expected span dimension. -/
theorem deficient_projection_iff (R U B : Submodule K V) (hRU : R ≤ U) (k : ℕ)
    (hB : finrank K ↥(R ⊔ B) = finrank K R + k) :
    finrank K ((U.map R.mkQ).map (Submodule.factor (le_sup_left : R ≤ R ⊔ B))) <
      min (finrank K (U.map R.mkQ)) (finrank K (V ⧸ (R ⊔ B))) ↔
    finrank K ↥(U ⊔ B) < min (finrank K U + k) (finrank K V) := by
  rw [← Submodule.map_comp, Submodule.factor_comp_mk]
  have hu := Quartic.QuotientBilinearImage.finrank_map_mkQ_add R U hRU
  have ht := (R ⊔ B).finrank_quotient_add_finrank
  have hi := image_finrank_add U (R ⊔ B)
  have he : U ⊔ (R ⊔ B) = U ⊔ B := by
    rw [← sup_assoc, sup_eq_left.mpr hRU]
  rw [he, hB] at hi
  rw [hB] at ht
  omega

/-- More vectors than the dimension of a containing subspace have zero exterior product. -/
theorem exterior_eq_zero_of_contained {m : ℕ} (S : Submodule K V)
    (w : Fin m → V) (hw : ∀ i, w i ∈ S) (hdim : finrank K S < m) :
    exteriorPower.ιMulti K m w = 0 := by
  apply AlternatingMap.map_linearDependent
  intro hi
  have hli : LinearIndependent K (fun i => (⟨w i,hw i⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hi
  have hc := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  omega

/-- In the deficient case, every exterior product using a basis-sized tuple
from the lift and the expected number of added relations vanishes. -/
theorem mixed_exterior_eq_zero (R U B : Submodule K V) (hRU : R ≤ U) (k : ℕ)
    (hB : finrank K ↥(R ⊔ B) = finrank K R + k)
    (hfail : finrank K ((U.map R.mkQ).map
        (Submodule.factor (le_sup_left : R ≤ R ⊔ B))) <
      min (finrank K (U.map R.mkQ)) (finrank K (V ⧸ (R ⊔ B))))
    (a : Fin (finrank K U) → V) (ha : ∀ i, a i ∈ U)
    (b : Fin (min k (finrank K V - finrank K U)) → V) (hb : ∀ i, b i ∈ B) :
    exteriorPower.ιMulti K _ (Fin.append a b) = 0 := by
  apply exterior_eq_zero_of_contained (U ⊔ B)
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using (show a j ∈ U ⊔ B from (le_sup_left : U ≤ U ⊔ B) (ha j))
    · simpa only [Fin.append_right] using (show b j ∈ U ⊔ B from (le_sup_right : B ≤ U ⊔ B) (hb j))
  · have hd := (deficient_projection_iff R U B hRU k hB).mp hfail
    have hu : finrank K U ≤ finrank K V := Submodule.finrank_le U
    omega

end Froberg.ProjectionFailure
