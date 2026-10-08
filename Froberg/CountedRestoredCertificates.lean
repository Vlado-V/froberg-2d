import Froberg.RestoredCountedOuterOdd
import Froberg.ActualRestoredIndependence
import Froberg.PreparedCountedRestoredOdd

/-! Full restored odd exactness at the actual all-even counts, with
arbitrary additional fixed columns and a late choice of output space. -/
noncomputable section
set_option maxHeartbeats 400000
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_all_even_restored_odd_open {d k h lo : ℕ}
    (hd : 3≤d) (heven : d%2=0) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (added : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
      (slot : Fin (finrank K (Forms K h d)) →
        Fin (Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))))),
      HasRestoredOuterOddOpen (m := n) (f := f n) (by omega : 1≤d) heven hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot := by
  let extra := fun n => e n+(∑ j∈activeHigherIndices d,higherGeneratorCount d h n j)+added
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hextra := prepared_extra_scalar_count_lower_order hd h added e he
  have hopen := exact_counts_restored_outer_odd_open (K := K) hd heven hk hh hhpos
    upper a f e extra ha hc hδ hreserve hextra
  filter_upwards [hopen] with n hn
  have hcard : upperCount n d+extra n=
      Fintype.card (Label (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added))) := by
    rw [allEvenLabel_card hd,preparedLabel_card,sum_targetLayerCount hd]
    dsimp only [extra]
    omega
  rw [hcard] at hn
  intro O hO slot
  exact hn (upperCount n d) (allEvenIndices d) (allEvenCount d h n (e n+added)) O hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => by have := (mem_allEvenIndices.mp hj).1; omega)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm slot

end Froberg.PreparedParameters
