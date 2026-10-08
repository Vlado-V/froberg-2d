import Froberg.RestoredCountedOuterOdd
import Froberg.PreparedAllEvenCounts

/-! The full restored odd row is exact on a nonempty open for the
manuscript's all-even layer counts, including fixed added quadratic slots. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_actual_restored_outer_odd_open {d k h lo : ℕ}
    (hd : 3≤d) (hdeven : d%2=0) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (added : ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) :
    ∀ᶠ n : ℕ in atTop,∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
      (slot : Fin (finrank K (Forms K h d)) →
        Fin (Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))))),
      HasRestoredOuterOddOpen (m := n) (f := f n) (by omega) hdeven hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot := by
  let extra := fun n => e n+(∑ j∈activeHigherIndices d,higherGeneratorCount d h n j)+added
  have hextra := prepared_extra_scalar_count_lower_order hd h added e (hc.mono fun n hn => hn.quadratic_upper)
  have hcount (n : ℕ) : upperCount n d+extra n=
      Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))) := by
    rw [allEvenLabel_card hd,←preparedScalarCount_eq_card hd]
    simp only [extra,preparedScalarCount]
    omega
  have hopen := exact_counts_restored_outer_odd_open (K := K)
    hd hdeven hk hh hhpos upper a f e extra ha hc hδ hreserve hextra
  filter_upwards [hopen] with n hn
  intro O hO slot
  rw [hcount] at hn
  exact hn (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added)) O hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (mem_allEvenIndices.mp hj).1; omega)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot

end Froberg.PreparedParameters
