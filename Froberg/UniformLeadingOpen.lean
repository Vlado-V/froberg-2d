module

public import Froberg.CountedLeadingOpen

@[expose] public section

/-! Leading-term thresholds independent of the infinite coefficient field. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial Quartic VectorMultiplicationCoordinates
open scoped Topology
namespace PreparedTarget

theorem eventually_uniform_private_dimension {h d u : ℕ} (hh : 0<h) (hd : 2≤d) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K], u ≤ finrank K (Rows K h n (d-1)) := by
  have hlim : Tendsto (fun n : ℕ => (u : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop (d-1) (by omega))
  have hcount := eventually_count_le_multiple_monomial (fun _ => u) h (d-1) 0 hlim
    (by have : (0 : ℝ)<h := by exact_mod_cast hh
        positivity)
  filter_upwards [hcount,eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  intro K _
  simpa only [Rows,Module.finrank_pi_fintype,Fintype.card_fin,
    finrank_forms K n (d-1) hnpos,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Nat.cast_id] using hn

theorem eventually_uniform_private_tuple_independent {h d u : ℕ} (hh : 0<h) (hd : 2≤d) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      ∃ P₀ : OuterSpace K (Fin h) n d u, LinearIndependent K P₀ := by
  filter_upwards [eventually_uniform_private_dimension (u := u) hh hd] with n hn
  intro K _ _
  exact private_tuple_independent_of_dimension (hn K)

end PreparedTarget
namespace PreparedParameters

theorem eventually_uniform_positive_leading_principal_open {h d u : ℕ}
    (hh : 0<h) (hd : 2≤d) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], ∀ (q f : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
      (O : ℕ → Submodule K (Poly K h)) (hO : ∀ j∈J,O j≤Forms K h j),
      (∀ j : J,∃ p : Space n d q J counts O,LinearIndependent K (p.2 j)) →
      HasLeadingPrivateOpen (n := n) (d := d) (q := q) (f := f) (u := u) (counts := counts) hO := by
  filter_upwards [PreparedTarget.eventually_uniform_private_dimension (u := u) hh hd]
    with n hn
  intro K _ _ q f J counts O hO hw
  exact positive_leading_principal_open_of_private_dimension hO hw (hn K)


end PreparedParameters
end Froberg
