import Froberg.CountedPrivatePreparedOpen
import Froberg.SmallCountedPrivateFrameOpen

/-! All odd degrees admit the full private split-reduction open on a
cofinal sequence of output dimensions. Frames and fixed pure tuples are
chosen after the scalar-size threshold. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial Filter PreparedParameters
variable {K : Type} [Field K] [Infinite K]

local instance allOddPrivatePreparedFrameFinite {h H m d q f u : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} (frame : Fin H → Forms K h 2) :
    Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts (privateFrameOutputs frame)) :=
  finite_fixedPureZeroScalarSpace (fun j _ => privateFrameOutputs_homogeneous frame j)

local instance allOddPrivatePreparedWitnessFinite {h H m d q : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} (frame : Fin H → Forms K h 2) :
    Module.Finite K (PreparedParameters.Space m d q J counts (privateFrameOutputs frame)) :=
  PreparedParameters.finite_space (fun j _ => privateFrameOutputs_homogeneous frame j)

def CountedPrivatePreparedAt {d : ℕ} (hd : 0<d) (hodd : d%2=1) (w : ℕ) : Prop :=
  ∀ (z extra : ℕ) (err : ℕ → ℕ),
    (∀ᶠ n : ℕ in atTop,(err n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
    ∀ᶠ v : ℕ in atTop,
      ∀ (t : ℕ) (ι : Fin t ↪ Fin z),
      ∃ (e : (Fin (2*w) → K) ≃ₗ[K] Forms K (2*w) 1)
        (columns : Fin t → Fin (2*w) → K)
        (P : MvPolynomial (Fin (finrank K
          (Fin (quadraticOutputDimension d (2*w)) → Forms K (2*w) 2))) K),
        (∀ i,columns i≠0) ∧ (∃ x,eval x P≠0) ∧
        ∀ frame : Fin (quadraticOutputDimension d (2*w)) → Forms K (2*w) 2,
          LinearIndependent K frame → eval ((Module.finBasis K _).equivFun frame) P≠0 →
          ∀ (f r : ℕ)
            (label : Fin r ≃ PreparedParameters.Label (upperCount (v+v+z) d) (allEvenIndices d)
              (allEvenCount d (2*w) (v+v+z) (err (v+v+z)+extra)))
            (U : Fin t → homogeneousSubmodule (Fin (2*w)) K d),
          let S := FixedPureZeroScalarSpace (v+v+z) d (upperCount (v+v+z) d) f t
            (allEvenIndices d) (allEvenCount d (2*w) (v+v+z) (err (v+v+z)+extra))
            (privateFrameOutputs frame)
          ∃ D : MvPolynomial (Fin (finrank K S)) K,
            (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
            ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
              PrivateSplitReduction hd hodd
                (fun j _ => privateFrameOutputs_homogeneous frame j)
                (fun j hj => (mem_allEvenIndices.mp hj).2.1)
                (fun j hj => (mem_allEvenIndices.mp hj).2.2) label U p

theorem eventually_counted_small_private_prepared_open {d : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → CountedPrivatePreparedAt (K := K) (by omega) hodd w := by
  filter_upwards [eventually_counted_small_private_frame_open (K := K) hd hd8 hodd] with w hw
  intro hfour z extra err herr
  filter_upwards [hw hfour z extra err herr] with v hv
  intro t ι
  obtain ⟨e,columns,P,hcolumns,hP,hgood⟩ := hv t ι
  refine ⟨e,columns,P,hcolumns,hP,?_⟩
  intro frame hframe hframeP f r label U
  obtain ⟨D,hD,hreduction⟩ := hgood frame hframe hframeP
  obtain ⟨p₀,hp₀⟩ := hD
  exact private_split_reduction_principal_open (by omega) hodd
    (fun j _ => privateFrameOutputs_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (fun j hj => lt_of_lt_of_le (by omega : 0<2) (mem_allEvenIndices.mp hj).1)
    label p₀ (privatePowerBiform (a := v+v) (d := d) (fun i => e (columns i)) ι)
    (hreduction p₀ hp₀) U

theorem eventually_counted_all_odd_private_prepared_open {d : ℕ}
    (hd : 3≤d) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → CountedPrivatePreparedAt (K := K) (by omega) hodd w := by
  by_cases hd9 : 9≤d
  · filter_upwards [eventually_counted_private_prepared_open (K := K) hd9 hodd] with w hw
    intro _
    exact hw
  · exact eventually_counted_small_private_prepared_open hd (by omega) hodd

/-- Here the paired half-size is `2*k`, so the actual output dimension is
`4*k`; no divisibility premise remains. -/
theorem eventually_counted_all_odd_private_prepared_cofinal {d : ℕ}
    (hd : 3≤d) (hodd : d%2=1) :
    ∀ᶠ k : ℕ in atTop,CountedPrivatePreparedAt (K := K) (by omega) hodd (2*k) := by
  obtain ⟨W,hW⟩ := eventually_atTop.mp
    (eventually_counted_all_odd_private_prepared_open (K := K) hd hodd)
  filter_upwards [eventually_ge_atTop W] with k hk
  exact hW (2*k) (by omega) ⟨k,by omega⟩

end Froberg.FullPreparedParameters
