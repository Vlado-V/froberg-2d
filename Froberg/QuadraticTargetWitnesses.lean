module

public import Froberg.QuadraticOutputDimension
public import Froberg.BiformExtension

@[expose] public section

/-! Exact-count witnesses for the two low target rows, with the actual
quadratic output dimension imposed. -/
noncomputable section
namespace Froberg
open Filter Module
open scoped Topology
variable (K : Type*) [Field K]

/-- Actual homogeneous generators in a quadratic output space of the
prescribed dimension, whose literal multiplication fills the target row. -/
def QuadraticTargetWitness (d h m r x y : ℕ) : Prop :=
  ∃ (W : Submodule K (Forms K h 2)) (o : Fin r → W) (f : Fin r → Forms K m (d-2)),
    finrank K W = quadraticOutputDimension d h ∧
    Function.Surjective (biformFamilyMap (x := x) (y := y) (fun i => (o i).val) f)

variable {K} [Infinite K]

theorem eventually_quadratic_row_three_exact {d : ℕ} (hd : 3 ≤ d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ r : ℕ,
      countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (r : ℝ) →
      QuadraticTargetWitness K d h m r 1 (d-1) := by
  have hδ : (1/6 : ℝ) < quadraticOutputDensity d :=
    lt_trans (by norm_num) (quadraticOutputDensity_lower hd)
  have he := eventually_quadratic_row_three (K := K) hd (quadraticOutputDimension d)
    (quadraticOutputDensity d) hδ (quadraticOutputDimension_limit hd)
    (Eventually.of_forall fun h => Nat.sub_le _ _)
  filter_upwards [he] with h hh
  filter_upwards [hh] with m hm
  intro r hr
  obtain ⟨W,o,f,hW,hs⟩ := hm
  obtain ⟨O,F,hF⟩ := biformFamily_surjective_extend_subspace W o f (Nat.ceil_le.mpr hr) hs
  exact ⟨W,O,F,hW,hF⟩

theorem eventually_quadratic_row_four_exact_of_endpoint {d : ℕ} (hd : 3 ≤ d)
    (hquad : ∀ h, 0 < h → GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ r : ℕ,
      countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (r : ℝ) →
      QuadraticTargetWitness K d h m r 2 (d-2) := by
  have hD : ∀ᶠ h : ℕ in atTop, upperCount h 2 ≤ quadraticOutputDimension d h ∧
      quadraticOutputDimension d h ≤ (h+1).choose 2 := by
    filter_upwards [upperCount_fits_quadraticOutputDimension hd] with h hh
    exact ⟨hh,Nat.sub_le _ _⟩
  have he := eventually_quadratic_row_four_of_endpoint hd hquad (quadraticOutputDimension d) hD
  filter_upwards [he] with h hh
  filter_upwards [hh] with m hm
  intro r hr
  obtain ⟨W,o,f,hW,hs⟩ := hm
  obtain ⟨O,F,hF⟩ := biformFamily_surjective_extend_subspace W o f (Nat.ceil_le.mpr hr) hs
  exact ⟨W,O,F,hW,hF⟩

end Froberg
