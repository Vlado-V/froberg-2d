import Froberg.PreparedOddParameterProjection
import Froberg.ScalarVectorRowsOpen

/-! The complete odd exactness statement holds on a nonempty principal
open of the actual prepared parameter space. The same open works for every
choice of the pure top forms. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f u t : ℕ} {G : ℝ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem prepared_odd_cycles_open (hh : 0<h) (hm : 0 < m) (hd : 3≤d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
    (D : MvPolynomial (Fin (finrank K (Fin (f+u) → Rows K h m (d-1)))) K)
    (hD : ∃ g : Fin (f+u) → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0)
    (hmodel : ∀ g : Fin (f+u) → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0 →
      VectorExpansionOpen.StrictModel g d G ∧
      Fintype.card (PreparedParameters.Label q J counts)*finrank K (VectorExpansionOpen.Source g)≤
        finrank K (VectorExpansionOpen.Target g d))
    (hscalar : HasOddScalarLayersOpen K h m d (f+u) (Fintype.card (PreparedParameters.Label q J counts)) t)
    (hupper : ((f+u)+(h+d-1).choose d)*(h+d-1).choose d≤
      (h+(d+1)-1).choose (d+1)*(m+(d-1)-1).choose (d-1)) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∃ P : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) P≠0) ∧
      ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) P≠0 →
        ∀ U : Fin u → Forms K h d,OddCyclesExact U p.1 p.2 := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  obtain ⟨P,hP,hgood⟩ := scalar_vector_rows_open hh hm (by omega) D hD hmodel hscalar hupper
  obtain ⟨E,hE,hEgood⟩ := principal_open_linear_pullback
    (preparedOddVectorParameters (K := K) (h := h) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) preparedOddVectorParameters_surjective P hP _ hgood
  refine ⟨E,hE,?_⟩
  intro p hp U
  obtain ⟨hfirst,hhigher⟩ := hEgood p hp
  exact odd_cycles_of_first_higher_rows hd hdodd hO hJ hpos heven U p.1 p.2 hfirst hhigher

end Froberg.PreparedTarget
