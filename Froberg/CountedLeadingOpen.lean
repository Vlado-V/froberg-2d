module

public import Froberg.PreparedCountedIndependence
public import Froberg.PreparedPositiveLeadingOpen

@[expose] public section

/-! A fixed private tuple is independent for sufficiently many scalar
variables. Together with the positive-layer witnesses this gives a
nonempty joint leading/private principal open on the full prepared space. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

namespace PreparedTarget

theorem private_tuple_independent_of_dimension {h n d u : ℕ}
    (hu : u ≤ finrank K (Rows K h n (d-1))) :
    ∃ P₀ : OuterSpace K (Fin h) n d u, LinearIndependent K P₀ := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank hu
  exact ⟨fun i => outerVectorEquiv (v i),
    hv.map' outerVectorEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr outerVectorEquiv.injective)⟩

omit [Infinite K] in
theorem eventually_private_dimension {h d u : ℕ} (hh : 0<h) (hd : 2≤d) :
    ∀ᶠ n : ℕ in atTop, u ≤ finrank K (Rows K h n (d-1)) := by
  have hlim : Tendsto (fun n : ℕ => (u : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop (d-1) (by omega))
  have hcount := eventually_count_le_multiple_monomial (fun _ => u) h (d-1) 0 hlim
    (by have : (0 : ℝ)<h := by exact_mod_cast hh
        positivity)
  filter_upwards [hcount,eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  simpa only [Rows,Module.finrank_pi_fintype,Fintype.card_fin,
    finrank_forms K n (d-1) hnpos,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Nat.cast_id] using hn

theorem eventually_private_tuple_independent {h d u : ℕ} (hh : 0<h) (hd : 2≤d) :
    ∀ᶠ n : ℕ in atTop,
      ∃ P₀ : OuterSpace K (Fin h) n d u, LinearIndependent K P₀ := by
  exact (eventually_private_dimension (K := K) (u := u) hh hd).mono
    fun _ hn => private_tuple_independent_of_dimension hn

end PreparedTarget

namespace PreparedParameters
variable {h n d q f u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

def HasLeadingPrivateOpen (hO : ∀ j∈J,O j≤Forms K h j) : Prop :=
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  ∃ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace n d q f u J counts O))) K,
    (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace n d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) D≠0 →
      (∀ j,LinearIndependent K (p.2.1.2 j)) ∧ LinearIndependent K p.1

theorem positive_leading_principal_open_of_private_dimension
    (hO : ∀ j∈J,O j≤Forms K h j)
    (hw : ∀ j : J,∃ p : Space n d q J counts O,LinearIndependent K (p.2 j))
    (hu : u ≤ finrank K (Rows K h n (d-1))) :
    HasLeadingPrivateOpen (n := n) (d := d) (q := q) (f := f) (u := u) (counts := counts) hO := by
  obtain ⟨P₀,hP₀⟩ := PreparedTarget.private_tuple_independent_of_dimension hu
  exact positive_leading_principal_open hO hw P₀ hP₀

theorem eventually_positive_leading_principal_open {h d u : ℕ}
    (hh : 0<h) (hd : 2≤d) :
    ∀ᶠ n : ℕ in atTop, ∀ (q f : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
      (O : ℕ → Submodule K (Poly K h)) (hO : ∀ j∈J,O j≤Forms K h j),
      (∀ j : J,∃ p : Space n d q J counts O,LinearIndependent K (p.2 j)) →
      HasLeadingPrivateOpen (n := n) (d := d) (q := q) (f := f) (u := u) (counts := counts) hO := by
  filter_upwards [PreparedTarget.eventually_private_dimension (K := K) (u := u) hh hd]
    with n hn
  intro q f J counts O hO hw
  exact positive_leading_principal_open_of_private_dimension hO hw hn

end PreparedParameters
end Froberg
