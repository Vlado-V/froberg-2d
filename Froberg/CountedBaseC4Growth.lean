module

public import Froberg.BaseC4Growth
public import Froberg.CountedTopGrowth
public import Froberg.PreparedOddScalarGrowth

@[expose] public section

/-! The exact base generator count gives simultaneous top and ordinary
growth before any positive-row scalar coefficients are chosen. -/
noncomputable section
set_option maxHeartbeats 500000
namespace Froberg
open Filter Module MvPolynomial Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h d b k lo : ℕ}

def BaseC4GrowthProperty {m f q : ℕ} (hd : 1 ≤ d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (t : ℕ)
    (p : OddScalarParameters K h m d f q) : Prop :=
  Function.Injective (projectedTopMap R (topGrowthParameters hd p.2 p.1)) ∧
  (∀ L : Submodule K (Fin b → K),t*finrank K L ≤
    finrank K (BilinearImage.image (projectedTopScalarAction R
      (topGrowthParameters hd p.2 p.1)) L)) ∧
  ∀ (j : ℕ) (hj : 3 ≤ j) (hjd : j ≤ d),
    OddScalarLayerProperty t (by omega) hjd (oddScalarBiformParameters p)

def HasBaseC4GrowthOpen {m f q : ℕ} (hd : 1 ≤ d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (t : ℕ) : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (OddScalarParameters K h m d f q))) K,
    (∃ p : OddScalarParameters K h m d f q,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → BaseC4GrowthProperty hd R t p

theorem has_base_c4_growth_open {m f q t : ℕ} (hd : 1 ≤ d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (htop : ProjectedTopGrowthOpen R m f q t)
    (hmid : HasOddScalarLayersOpen K h m d f q t) :
    HasBaseC4GrowthOpen (m := m) (f := f) (q := q) hd R t :=
  base_c4_growth_open hd R htop hmid

theorem eventually_counted_base_c4_growth (hd : 3 ≤ d) (hh : 0 < h) (hb : 0 < b)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h (d-1)),b*finrank K L ≤
      finrank K (Forms K h (d-1))*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := d-1)) L).map R))
    (hratio : (h : ℝ)/(2*((1+(d-1) : ℕ) : ℝ)) ≤
      (b : ℝ)/((h+(d-1)-1).choose (d-1) : ℝ))
    (upper : Bool) (a f e : ℕ → ℕ)
    (hcounts : ∀ᶠ m in atTop,ExactCountConditions d k h lo m (a m) (f m) (e m) upper) :
    ∀ᶠ m : ℕ in atTop,
      HasBaseC4GrowthOpen (m := m) (f := f m) (q := upperCount m d)
        (by omega : 1 ≤ d) R (scalarReserveCount d m) := by
  have hd' : 1+(d-1)=d := by omega
  have ht := eventually_counted_top_growth hh (by omega : 2 ≤ d-1) hb
    R hP hratio upper a f e (by simpa only [hd'] using hcounts)
  have hm := eventually_counted_odd_scalar_growth (K := K) hd hh upper a f e hcounts
  simp only [hd'] at ht
  filter_upwards [ht,hm] with m htop hmid
  apply has_base_c4_growth_open (by omega : 1 ≤ d) R htop
  exact hmid

end Froberg
