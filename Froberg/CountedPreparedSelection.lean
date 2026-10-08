import Froberg.CountedPreparedFrames
import Froberg.AllScalarPrivatePreparedOpen
import Froberg.CountedPreparedOuterOpen
import Froberg.CountedLeadingOpen
import Froberg.FrameEvenData
import Froberg.EnlargedPreparedOpen

/-! A single frame and its actual coefficient spaces supply every
certificate of the odd-degree critical comparison. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg PreparedParameters FullPreparedParameters Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]

structure PreparedFrameReady {d h u : ℕ} (hd : 3≤d) (ho : d%2=1) (n f e : ℕ)
    (U : Fin u → Forms K h d)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2) : Prop where
  independent : LinearIndependent K frame
  base : HasBasicOpen (m := n) (q := upperCount n d) (f := f)
    (counts := allEvenCount d h n e) (by omega : 0<d)
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) U
  enlarged : HasEnlargedPreparedOpen (m := n) (q := upperCount n d) (f := f)
    (counts := allEvenCount d h n (e+1)) (by omega : 0<d) ho
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm U

theorem eventually_counted_prepared_frame_ready {d : ℕ} (hd : 3≤d) (ho : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w → ∀ (k lo : ℕ),0<k → 2*w=k*centralHalfBinomial d → 0<2*w →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k (2*w) lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d (2*w) n (f n)) →
      ∀ u : ℕ,∀ᶠ n : ℕ in atTop,
        ∀ U : Fin u → Forms K (2*w) d,PureFamilyAdmissible U →
        ∃ frame : Fin (quadraticOutputDimension d (2*w)) → Forms K (2*w) 2,
          PreparedFrameReady hd ho n (f n) (e n) U frame := by
  have hdouble : Tendsto (fun w : ℕ => 2*w) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with w hw
    omega
  filter_upwards [hdouble.eventually (eventually_counted_prepared_frames (K := K) hd ho),
    hdouble.eventually (eventually_frame_even_data (K := K) hd),
    hdouble.eventually (eventually_allEven_prepared_outer_open (K := K) hd ho),
    eventually_counted_all_odd_private_prepared_all_scalars (K := K) hd ho]
    with w hframes heven houter hprivate
  intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres u
  have he := hc.mono fun n hn => hn.quadratic_upper
  have hf := hframes k lo hk hkh hhpos upper a f e ha hc δ hδ hres u
  have hl := heven hdiv 1 e he
  have ho' := houter e f he (exact_conditions_outer_limit hd upper a f e hc) u
  have he' : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  have hp := hprivate hdiv 1 e he' u
  have hleading := eventually_positive_leading_principal_open (K := K) (u := u) hhpos (by omega : 2≤d)
  filter_upwards [hf,hl,ho',hp,hleading] with n hfn hln hon hpn hleadn
  intro U hU
  obtain ⟨D,hD,hDgood⟩ := hfn
  obtain ⟨E,hE,hEgood⟩ := hon
  obtain ⟨P,hP,hPgood⟩ := hpn
  obtain ⟨x,hxD,hxE⟩ := principal_opens_intersect hD hE
  have hDE : ∃ x,eval x (D*E)≠0 := ⟨x,by simpa only [map_mul] using mul_ne_zero hxD hxE⟩
  obtain ⟨y,hyDE,hyP⟩ := principal_opens_intersect hDE hP
  have hy : eval y D≠0 ∧ eval y E≠0 := by simpa only [map_mul,mul_ne_zero_iff] using hyDE
  let frame := (Module.finBasis K (Fin (quadraticOutputDimension d (2*w)) → Forms K (2*w) 2)).equivFun.symm y
  have hDframe : eval ((Module.finBasis K _).equivFun frame) D≠0 := by
    simpa only [frame,LinearEquiv.apply_symm_apply] using hy.1
  have hEframe : eval ((Module.finBasis K _).equivFun frame) E≠0 := by
    simpa only [frame,LinearEquiv.apply_symm_apply] using hy.2
  have hPframe : eval ((Module.finBasis K _).equivFun frame) P≠0 := by
    simpa only [frame,LinearEquiv.apply_symm_apply] using hyP
  obtain ⟨hfi,hpair⟩ := hDgood frame hDframe
  let hO := fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j
  have hlead := hleadn (upperCount n d) (f n) (allEvenIndices d)
    (allEvenCount d (2*w) n (e n+1)) (targetLayerOutput frame) hO (hln frame hfi).1
  have hsep := hEgood frame hEframe (targetLayerOutput frame) hO
    (by change outputFrameSpace frame≤outputFrameSpace frame; exact le_rfl)
  have hred := hPgood frame hfi hPframe (f n) _ (Fintype.equivFin _).symm U
  refine ⟨frame,⟨hfi,(hpair U hU).1,?_⟩⟩
  exact hasEnlargedPreparedOpen_of_opens (by omega : 0<d) ho hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm U
    (hpair U hU).2 hlead hred hsep

end Froberg.PreparedTarget
