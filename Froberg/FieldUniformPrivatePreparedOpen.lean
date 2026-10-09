module

public import Froberg.FieldUniformPrivateFrame
public import Froberg.AllScalarPrivatePreparedOpen

@[expose] public section

/-! The frame and coefficient opens are constructed after numeric thresholds
that are independent of the infinite coefficient field. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial Filter PreparedParameters
variable {K : Type} [Field K] [Infinite K]

local instance fieldUniformPreparedFrameFinite {h H m d q f u : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} (frame : Fin H → Forms K h 2) :
    Module.Finite K (FixedPureZeroScalarSpace m d q f u J counts (privateFrameOutputs frame)) :=
  finite_fixedPureZeroScalarSpace (fun j _ => privateFrameOutputs_homogeneous frame j)

local instance fieldUniformPreparedWitnessFinite {h H m d q : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} (frame : Fin H → Forms K h 2) :
    Module.Finite K (PreparedParameters.Space m d q J counts (privateFrameOutputs frame)) :=
  PreparedParameters.finite_space (fun j _ => privateFrameOutputs_homogeneous frame j)

theorem eventually_uniform_counted_all_odd_private_prepared_all_scalars {d : ℕ}
    (hd : 3≤d) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (extra : ℕ) (err : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(err n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ u : ℕ,∀ᶠ n : ℕ in atTop,
        ∀ (K : Type) [Field K] [Infinite K],
        PrivatePreparedFrameOpen (K := K) (by omega) hodd (2*w) n u (err n+extra) := by
  classical
  filter_upwards [eventually_field_uniform_private_frame_open hd hodd] with w hw
  intro hdiv extra err herr u
  have hs (z : ℕ) (ι : Fin u ↪ Fin z) :
      ∀ᶠ v : ℕ in atTop,∀ (K : Type) [Field K] [Infinite K],
        PrivatePreparedFrameOpen (K := K) (by omega) hodd (2*w) (v+v+z) u
          (err (v+v+z)+extra) := by
    filter_upwards [hw hdiv z extra err herr] with v hv
    intro K _ _
    obtain ⟨e,columns,P,hcolumns,hP,hgood⟩ := hv K u ι
    refine ⟨P,hP,?_⟩
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
  exact eventually_of_twice_add_shifts u _
    (hs u (Function.Embedding.refl (Fin u)))
    (hs (u+1) ⟨Fin.castAdd 1,Fin.castAdd_injective u 1⟩)

end Froberg.FullPreparedParameters
