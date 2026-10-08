import Froberg.RestoredQuadraticSeparationOpen
import Froberg.ScalarCoefficientWitness

/-! Actual scalar and outer counts supply a restored C.2 coefficient open.
The variable threshold is chosen before the restored coefficient spaces and
all choices of output detector. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedParameters
open Froberg Module Filter MvPolynomial
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

/-- The paired C.1 scalar witness supplies Q and C internally, uniformly in
all restored parameters and output detectors chosen after the threshold. -/
theorem eventually_restored_counted_quadratic_separation
    {d h : ℕ} (hd : 3≤d) (hh : 0<h) (r f : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1))
      atTop (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop, ∀ q c : ℕ, ∀ (J : Finset ℕ) (counts : ℕ → ℕ)
      (O : ℕ → Submodule K (Poly K h)) (hO : ∀ j∈J,O j≤Forms K h j)
      (idx : Fin (r n) ≃ Label q J counts)
      (I : Type) [Fintype I] [DecidableEq I],
      Fintype.card I=outerColumnCount d h →
      ∀ (T : Poly K h →ₗ[K] (Fin c → K)) (o : I → Forms K h 1),
        LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)) →
      letI : Module.Finite K (Space n d q J counts O) := finite_space hO
      ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace n d q (f n) J counts O))) K,
        (∃ p : RestoredOuterSpace n d q (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0) ∧
        ∀ p : RestoredOuterSpace n d q (f n) J counts O,
          eval ((Module.finBasis K _).equivFun p) D≠0 →
            QuadraticSeparated T (restoredC2Projection idx p) := by
  have hs := eventually_scalar_coefficient_witnesses_capacity_shift (K := K) hd hh r f hr hf 0
  simp only [Nat.add_zero] at hs
  filter_upwards [hs] with n hn
  classical
  obtain ⟨S,hSuniv,hScard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := n/2)
      (by simpa only [Finset.card_univ,Fintype.card_fin] using Nat.div_le_self n 2)
  have hsum : S.card+Sᶜ.card=n := by simp
  have hS : S.card≤Sᶜ.card := by omega
  have hS' : Sᶜ.card≤S.card+1 := by omega
  obtain ⟨D,⟨Q,hQ⟩,hgood⟩ := hn S hS hS'
  obtain ⟨hprefix,C,hCdeg,hCdim,hC,hCQ,hcap⟩ := hgood Q hQ
  intro q c J counts O hO idx I _ _ hI T o ho
  apply restored_quadratic_separation_open_of_scalar_space hO idx T Q
    (hprefix (d-2) le_rfl) o ho C hCdeg hC hCQ
  simpa only [hI] using hcap

end Froberg.PreparedParameters
