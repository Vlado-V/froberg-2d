module

public import Froberg.AllOddCountedPrivatePreparedOpen
public import Froberg.NaturalEventualParity
public import Froberg.TargetLayerAssembly

@[expose] public section

/-! The full private split reduction at every sufficiently large total
scalar dimension, with the frame chosen after that dimension. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial Filter PreparedParameters
variable {K : Type} [Field K] [Infinite K]

local instance allScalarPrivateFrameFinite {h H n d q f u : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} (frame : Fin H → Forms K h 2) :
    Module.Finite K (FixedPureZeroScalarSpace n d q f u J counts (targetLayerOutput frame)) :=
  finite_fixedPureZeroScalarSpace (fun j _ => targetLayerOutput_homogeneous frame j)

def PrivatePreparedFrameOpen {d : ℕ} (hd : 0<d) (hodd : d%2=1)
    (h n u e : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin (finrank K
      (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
    (∃ x,eval x P≠0) ∧
    ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
      LinearIndependent K frame → eval ((Module.finBasis K _).equivFun frame) P≠0 →
      ∀ (f r : ℕ)
        (label : Fin r ≃ PreparedParameters.Label (upperCount n d) (allEvenIndices d)
          (allEvenCount d h n e))
        (U : Fin u → homogeneousSubmodule (Fin h) K d),
      let S := FixedPureZeroScalarSpace n d (upperCount n d) f u (allEvenIndices d)
        (allEvenCount d h n e) (targetLayerOutput frame)
      ∃ D : MvPolynomial (Fin (finrank K S)) K,
        (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
        ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
          PrivateSplitReduction hd hodd
            (fun j _ => targetLayerOutput_homogeneous frame j)
            (fun j hj => (mem_allEvenIndices.mp hj).2.1)
            (fun j hj => (mem_allEvenIndices.mp hj).2.2) label U p

theorem counted_private_prepared_all_scalars {d w : ℕ}
    (hd : 0<d) (hodd : d%2=1)
    (hw : CountedPrivatePreparedAt (K := K) hd hodd w)
    (extra : ℕ) (err : ℕ → ℕ)
    (herr : ∀ᶠ n : ℕ in atTop,
      (err n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) (u : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      PrivatePreparedFrameOpen (K := K) hd hodd (2*w) n u (err n+extra) := by
  apply eventually_of_twice_add_shifts u
    (fun n => PrivatePreparedFrameOpen (K := K) hd hodd (2*w) n u (err n+extra))
  · filter_upwards [hw u extra err herr] with v hv
    obtain ⟨e,columns,P,hcolumns,hP,hgood⟩ := hv u (Function.Embedding.refl (Fin u))
    refine ⟨P,hP,?_⟩
    intro frame hframe hframeP f r label U
    exact hgood frame hframe hframeP f r label U
  · filter_upwards [hw (u+1) extra err herr] with v hv
    let ι : Fin u ↪ Fin (u+1) := ⟨Fin.castAdd 1,Fin.castAdd_injective u 1⟩
    obtain ⟨e,columns,P,hcolumns,hP,hgood⟩ := hv u ι
    refine ⟨P,hP,?_⟩
    intro frame hframe hframeP f r label U
    exact hgood frame hframe hframeP f r label U

theorem eventually_counted_all_odd_private_prepared_all_scalars {d : ℕ}
    (hd : 3≤d) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (extra : ℕ) (err : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(err n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ u : ℕ,∀ᶠ n : ℕ in atTop,
        PrivatePreparedFrameOpen (K := K) (by omega) hodd (2*w) n u (err n+extra) := by
  filter_upwards [eventually_counted_all_odd_private_prepared_open (K := K) hd hodd] with w hw
  intro hdiv extra err herr u
  exact counted_private_prepared_all_scalars (by omega) hodd (hw hdiv) extra err herr u

end Froberg.FullPreparedParameters
