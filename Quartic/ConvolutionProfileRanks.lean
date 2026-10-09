module

public import Quartic.ConvolutionProfileImage
public import Quartic.LayerRankCounts

@[expose] public section

/-!
# Actual ranks of the free-monomial image layers

The sharp-profile rank hypotheses are proved here for actual quotient subspaces,
using core shadows and the one- and two-degree output multiplication estimates.
-/
noncomputable section
namespace Quartic.ConvolutionProfileRanks
open FreeMonomialCounts ConvolutionFreePieces ConvolutionProfileImage
open ConvolutionCoreImages LayerRankCounts ProfileCertificate
variable {K : Type*} [Field K] {t w : ℕ}

/-- Output blocks have at most three independent classes. -/
theorem output_rank_le_three (D : Submodule K (Piece K t 0 0)) :
    Module.finrank K D ≤ 3 := by
  have h := Submodule.finrank_le D
  rw [corePieceZero_finrank] at h
  exact h

/-- The core source rank has its actual Hilbert-function bound. -/
theorem core_rank_le (ht : 2 ≤ t) (L : Submodule K (Piece K t 0 1)) :
    Module.finrank K L ≤ 2 * (t - 1) := by
  have h := Submodule.finrank_le L
  rw [corePieceOne_finrank ht] at h
  exact h

theorem linear_rank_base [Infinite K] (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) (D : Fin w → Submodule K (Piece K t 0 0)) (i : Fin w) :
    t.choose 2 - (t - (Module.finrank K L + 1) / 2).choose 2 ≤
      Module.finrank K (linearLayer L D i) :=
  (coreLinearImage_sharp_bound ht L).trans (Submodule.finrank_mono le_sup_left)

theorem linear_rank_full (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) (D : Fin w → Submodule K (Piece K t 0 0))
    (i : Fin w) (hi : 0 < Module.finrank K (D i)) :
    t.choose 2 ≤ Module.finrank K (linearLayer L D i) := by
  have hD : D i ≠ ⊥ := by
    intro h
    have hz : Module.finrank K (D i) = 0 := Submodule.finrank_eq_zero.mpr h
    omega
  have he : linearLayer L D i = ⊤ := by
    unfold linearLayer
    rw [outputImage_two_eq_top hD, sup_top_eq]
  rw [he, finrank_top, corePieceTwo_finrank ht]

theorem quadratic_rank_base (L : Submodule K (Piece K t 0 1))
    (D : Fin w → Submodule K (Piece K t 0 0)) (b : ExactExponent w 2) :
    Module.finrank K L ≤ Module.finrank K (quadraticLayer L D b) :=
  Submodule.finrank_mono le_sup_left

theorem quadratic_rank_incident (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) (D : Fin w → Submodule K (Piece K t 0 0))
    (b : ExactExponent w 2) (i : Fin w) (hi : 0 < b.val i) :
    min (Module.finrank K (D i)) 2 * (t - 1) ≤ Module.finrank K (quadraticLayer L D b) := by
  apply (outputImage_one_bound ht (D i)).trans
  apply Submodule.finrank_mono
  exact le_sup_of_le_right (le_iSup (fun j : {j : Fin w // 0 < b.val j} => outputImage 1 (D j.val)) ⟨i, hi⟩)

theorem quadratic_rank_meets_one (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) (D : Fin w → Submodule K (Piece K t 0 0))
    (b : ExactExponent w 2) (hb : Meets (fun i => Module.finrank K (D i)) 1 b) :
    t - 1 ≤ Module.finrank K (quadraticLayer L D b) := by
  obtain ⟨i, hdim, hi⟩ := hb
  have h := quadratic_rank_incident ht L D b i hi
  have hm : 1 ≤ min (Module.finrank K (D i)) 2 := le_min hdim (by decide)
  nlinarith

theorem quadratic_rank_meets_two (ht : 2 ≤ t)
    (L : Submodule K (Piece K t 0 1)) (D : Fin w → Submodule K (Piece K t 0 0))
    (b : ExactExponent w 2) (hb : Meets (fun i => Module.finrank K (D i)) 2 b) :
    2 * (t - 1) ≤ Module.finrank K (quadraticLayer L D b) := by
  obtain ⟨i, hdim, hi⟩ := hb
  have h := quadratic_rank_incident ht L D b i hi
  simpa only [min_eq_right hdim] using h

theorem cubic_rank_incident (D : Fin w → Submodule K (Piece K t 0 0))
    (b : ExactExponent w 3) (i : Fin w) (hi : 0 < b.val i) :
    Module.finrank K (D i) ≤ Module.finrank K (cubicLayer D b) :=
  Submodule.finrank_mono (le_iSup (fun j : {j : Fin w // 0 < b.val j} => D j.val) ⟨i, hi⟩)

/-- The actual core shadow has exactly the manuscript's integer profile value. -/
theorem source_linear_rank_base [Infinite K] (c : ℕ) (hc : 4 ≤ c)
    (L : Submodule K (Piece K (coreP c + 1) 0 1))
    (D : Fin w → Submodule K (Piece K (coreP c + 1) 0 0)) (i : Fin w) :
    SharpCertificate.coreShadow c (Module.finrank K L) ≤
      (Module.finrank K (linearLayer L D i) : ℤ) := by
  have ht : 2 ≤ coreP c + 1 := by unfold coreP; omega
  have hdim := core_rank_le ht L
  have hh : (Module.finrank K L + 1) / 2 ≤ coreP c := by omega
  have he : coreP c + 1 - (Module.finrank K L + 1) / 2 =
      coreP c - (Module.finrank K L + 1) / 2 + 1 := by omega
  have h := linear_rank_base ht L D i
  rw [he] at h
  rw [SharpCertificate.coreShadow_eq_binomial, coreB_eq_binomial]
  omega

/-- The numerical sharp expression is a lower bound on the actual sum of layer ranks. -/
theorem source_sharp_le_layer_sum [Infinite K] (m c : ℕ) (hc : 4 ≤ c)
    (L : Submodule K (Piece K (coreP c + 1) 0 1))
    (D : Fin (freeW m c) → Submodule K (Piece K (coreP c + 1) 0 0)) :
    UniformSurplus.sourceSharp m c (Module.finrank K L)
      (levelCount (fun i => Module.finrank K (D i)) 1)
      (levelCount (fun i => Module.finrank K (D i)) 2)
      (levelCount (fun i => Module.finrank K (D i)) 3) ≤
      (((∑i, Module.finrank K (linearLayer L D i)) +
        (∑b, Module.finrank K (quadraticLayer L D b)) +
        (∑b, Module.finrank K (cubicLayer D b)) : ℕ) : ℝ) := by
  have ht : 2 ≤ coreP c + 1 := by unfold coreP; omega
  apply source_sharp_rank_sum m c (Module.finrank K L)
  · simpa only [coreA, Nat.add_sub_cancel] using core_rank_le ht L
  · exact source_linear_rank_base c hc L D
  · intro i hi
    rw [coreB_eq_binomial]
    exact_mod_cast linear_rank_full ht L D i hi
  · exact quadratic_rank_base L D
  · intro b hb
    simpa only [Nat.add_sub_cancel] using quadratic_rank_meets_one ht L D b hb
  · intro b hb
    simpa only [coreA, Nat.add_sub_cancel] using quadratic_rank_meets_two ht L D b hb
  · exact cubic_rank_incident D

end Quartic.ConvolutionProfileRanks
