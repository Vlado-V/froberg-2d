module

public import Froberg.FrameEvenData
public import Froberg.FieldUniformAllDegreeEvenData

@[expose] public section

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Filter Module MvPolynomial

theorem eventually_uniform_frame_even_data {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop,4∣h → ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      ∀ᶠ n : ℕ in atTop,
        ∀ (K : Type) [Field K] [Infinite K],
        ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
          LinearIndependent K frame → FrameEvenData d n (e n+extra) frame := by
  filter_upwards [eventually_field_uniform_all_degree_even_data hd,
    block_parameters_eventually hd,eventually_gt_atTop (0 : ℕ)] with h hh hblock hhpos
  intro hdiv extra e he
  filter_upwards [hh hdiv extra e he] with n hn
  intro K _ _ frame hframe
  let c := frameQuotientDimension frame
  let T := canonicalFrameConstraint frame
  have hc : finrank K (Fin c → K)=deletedTargetCount d h := by
    simpa only [Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] using
      canonicalFrameConstraint_dimension hhpos hblock.1 frame hframe
  have hO : finrank K ↥(Forms K h 2 ⊓ (T 2).ker)=quadraticOutputDimension d h := by
    rw [canonicalFrameConstraint_outputs]
    change finrank K ↥(outputFrameSpace frame)=quadraticOutputDimension d h
    exact outputFrameSpace_finrank frame hframe
  have hT : ∀ R,4≤R → T R=0 := fun _ hR => canonicalFrameConstraint_ge_four frame hR
  have H := hn K (Fin c → K) T hc hO hT
  have hOeq : (fun j => Forms K h j ⊓ (T j).ker)=targetLayerOutput frame :=
    funext (canonicalFrameConstraint_outputs frame)
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (allEvenCount d h n (e n+extra)) (fun j => Forms K h j ⊓ (T j).ker)) :=
    finite_space (fun _ _ => inf_le_left)
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (allEvenCount d h n (e n+extra)) (targetLayerOutput frame)) :=
    finite_space (fun j _ => targetLayerOutput_homogeneous frame j)
  exact ⟨(leading_witnesses_congr_outputs hOeq).mp H.1,
    (evenReductionOpen_congr_outputs hOeq).mp H.2⟩

end Froberg.PreparedParameters
