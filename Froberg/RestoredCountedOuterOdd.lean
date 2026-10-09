module

public import Froberg.RestoredOuterOddOpen
public import Froberg.CountedScalarVectorRows
public import Froberg.PreparedScalarReserve

@[expose] public section

/-! Actual-count full odd exactness for a restored even family with all
its outer generators. The scalar overhead may include fixed extra slots. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

def HasRestoredOuterOddOpen {h m d q r f : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (Poly K h)} (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r) : Prop :=
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  ∃ P : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
    (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
    ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0 →
      OddSplitExact (restoredBiformFamily hd hO hJ heven idx slot p.1)
        (fun j => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 j)))

theorem restored_outer_odd_open_of_rows {h m d q r f : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (Poly K h)} (hd : 3≤d) (hdeven : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (P : MvPolynomial (Fin (finrank K (ScalarVectorParameters K h m d f r))) K)
    (hP : ∃ p : ScalarVectorParameters K h m d f r,eval ((Module.finBasis K _).equivFun p) P≠0)
    (hgood : ∀ p : ScalarVectorParameters K h m d f r,eval ((Module.finBasis K _).equivFun p) P≠0 →
      FirstVectorRowExact p.2 p.1 ∧ HigherOddRows p.2 p.1) :
    HasRestoredOuterOddOpen (m := m) (f := f) (by omega) hdeven hO hJ heven idx slot := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  obtain ⟨E,hE,hEgood⟩ := principal_open_linear_pullback (restoredOuterVectorParameters (O := O) idx)
    (restoredOuterVectorParameters_surjective idx) P hP _ hgood
  refine ⟨E,hE,?_⟩
  intro p hp
  obtain ⟨hfirst,hhigher⟩ := hEgood p hp
  exact filtered_even_odd_exact hd (restoredBiformFamily hdeven hO hJ heven idx slot p.1)
    (fun i => p.1.1.1 (idx i)) (fun j => PreparedTarget.outerVectorEquiv.symm (p.2 j))
    (restoredBiformFamily_scalar_component (by omega) hdeven hO hJ heven hpos idx slot p.1)
    hfirst hhigher

theorem exact_counts_restored_outer_odd_open {d k h lo : ℕ}
    (hd : 3≤d) (hdeven : d%2=0) (hk : 0<k) (hh : h=k*centralHalfBinomial d) (hhpos : 0<h)
    (upper : Bool) (a f e extra : ℕ → ℕ) (ha : ∀ n,a n≤n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0<δ)
    (hreserve : ∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n))
    (hextra : Tendsto (fun n : ℕ => (extra n : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,∀ (q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
      (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
      (idx : Fin (upperCount n d+extra n) ≃ Label q J counts)
      (slot : Fin (finrank K (Forms K h d)) → Fin (upperCount n d+extra n)),
      HasRestoredOuterOddOpen (m := n) (f := f n) (by omega) hdeven hO hJ heven idx slot := by
  have hopen := exact_counts_scalar_vector_rows_open (K := K) (b := 0)
    hd hk hh hhpos upper a f e extra ha hc hδ hreserve hextra
  simp only [Nat.add_zero] at hopen
  filter_upwards [hopen] with n hn
  intro q J counts O hO hJ hpos heven idx slot
  obtain ⟨P,hP,hgood⟩ := hn
  exact restored_outer_odd_open_of_rows hd hdeven hO hJ hpos heven idx slot P hP hgood

end Froberg.PreparedParameters
