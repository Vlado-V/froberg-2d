import Froberg.PreparedActualCubicPrivateUniform
import Froberg.PreparedActualMiddlePrivateUniform
import Froberg.PrivateFrameReduction
import Froberg.PrivateFrameReference
import Froberg.PrivateFrameNonzero
import Froberg.PrivateDetectorCapacity

/-! In odd degrees three, five and seven, one nonempty frame open supports
a fixed nonzero private tuple and the actual counted prepared-family open.
The frame is selected after the scalar threshold. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter PrivateColumns
variable {K : Type} [Field K] [Infinite K]

local instance smallCountedPrivateFrameSpaceFinite {h H n d q : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} (frame : Fin H → Forms K h 2) :
    Module.Finite K (Space n d q J counts (privateFrameOutputs frame)) :=
  finite_space (fun j _ => privateFrameOutputs_homogeneous frame j)

local instance smallCountedPrivateConstrainedFinite {X : Type*} [AddCommGroup X] [Module K X]
    {w n d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) :
    Module.Finite K (Space n d q J counts (constrainedOutputs T)) :=
  finite_space (fun _ _ => inf_le_left)

theorem eventually_actual_small_private_reduction_open_uniform {d : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      T 4=0 →
        ∀ (t c H : ℕ)
          (bo : Basis (Fin H) K (homogeneousSubmodule (Fin w × Bool) K 1))
          (l : Fin t → homogeneousSubmodule (Fin w × Bool) K 1),
        (∀ i,l i≠0) →
        ∀ (ι : Fin t ↪ Fin z)
          (L : MvPolynomial (Fin w × Bool) K →ₗ[K] (Fin c → K)),
        constrainedOutputs T 2≤L.ker →
        ∀ A : Fin t → (Fin H → K) →ₗ[K] (Fin c → K),
        (∀ i j,L ((l i).val*(bo j).val)=A i (Pi.single j 1)) →
        (privatePolynomialMap (a := v+v) (s := d-1) ι A).ker=
          Submodule.span K (Set.range (koszulVector
            (privateGenerator (a := v+v) (s := d-1) ι (fun i => bo.equivFun (l i))))) →
        let S := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
            PrivatePositiveReduction p (privatePowerBiform (a := v+v) (d := d) l ι) := by
  by_cases h3 : d=3
  · subst d
    filter_upwards [eventually_actual_cubic_private_reduction_open_uniform (K := K)] with w hw
    intro _ z extra e he
    filter_upwards [hw z extra e he] with v hv
    intro X _ _ _ T hX hO _
    exact hv X T hX hO
  · exact eventually_actual_middle_private_reduction_open_uniform (K := K) (by omega) hd8 hodd

theorem eventually_counted_small_private_frame_reduction_open {d : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
      ∀ (z extra : ℕ) (err : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(err n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        ∀ (t : ℕ) (frame : Fin (quadraticOutputDimension d (2*w)) → Forms K (2*w) 2),
        LinearIndependent K frame →
        ∀ (e : (Fin (2*w) → K) ≃ₗ[K] Forms K (2*w) 1)
          (columns : Fin t → Fin (2*w) → K),
        (∀ i,columns i≠0) →
        ∀ (ι : Fin t ↪ Fin z)
          (L₀ : Forms K (2*w) 2 →ₗ[K]
            (Fin (finrank K (Forms K (2*w) 2 ⧸ Submodule.span K (Set.range frame))) → K)),
        L₀.ker=Submodule.span K (Set.range frame) →
        (privatePolynomialMap (a := v+v) (s := d-1) ι
          (fun i => (L₀.comp (mulForm (e (columns i)))).comp e.toLinearMap)).ker=
          Submodule.span K (Set.range (koszulVector
            (privateGenerator (a := v+v) (s := d-1) ι columns))) →
        let S := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (err (v+v+z)+extra)) (privateFrameOutputs frame)
        ∃ D : MvPolynomial (Fin (finrank K S)) K,
          (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
          ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 →
            PrivatePositiveReduction p
              (privatePowerBiform (a := v+v) (d := d) (fun i => e (columns i)) ι) := by
  classical
  obtain ⟨W,hW⟩ := eventually_atTop.mp (block_parameters_eventually (by omega : 3≤d))
  have hb : ∀ᶠ w : ℕ in atTop,outerColumnCount d (2*w)≤2*w := by
    filter_upwards [eventually_ge_atTop W] with w hw
    exact (hW (2*w) (by omega)).1
  filter_upwards [eventually_actual_small_private_reduction_open_uniform (K := K) hd hd8 hodd,
    hb,eventually_gt_atTop 0] with w hw hblock hwpos
  have hdel : deletedTargetCount d (2*w)≤(2*w+1).choose 2 :=
    Nat.choose_le_choose 2 (Nat.add_le_add_right hblock 1)
  intro hdiv z extra err herr
  filter_upwards [hw hdiv z extra err herr] with v hv
  intro t frame hframe e columns hcolumns ι L₀ hL₀ hprivate
  let f := pairedOutputEquiv w
  let c := finrank K (Forms K (2*w) 2 ⧸ Submodule.span K (Set.range frame))
  have hc : c=deletedTargetCount d (2*w) := by
    dsimp only [c]
    rw [quadratic_frame_quotient_finrank frame hframe,
      finrank_forms K (2*w) 2 (by omega)]
    simp only [quadraticOutputDimension,show 2*w+2-1=2*w+1 by omega]
    exact Nat.sub_sub_self hdel
  let T := pairedFrameConstraint f L₀
  have hX : finrank K (Fin c → K)=deletedTargetCount d (2*w) := by
    simpa only [Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] using hc
  have hO : finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) :=
    pairedFrameConstraint_space_finrank f frame hframe L₀ hL₀
  have hT : ∀ R,4≤R → T R=0 := fun _ hR => pairedFrameConstraint_ge_four f L₀ hR
  let bo := renamedPrivateBasis f e
  let l := fun i => renamedPrivateColumn f e (columns i)
  let L := (quadraticPolynomialDetector L₀).comp (rename f).toLinearMap
  let A := fun i => (L₀.comp (mulForm (e (columns i)))).comp e.toLinearMap
  have hl : ∀ i,l i≠0 := fun i => renamedPrivateColumn_ne_zero f e (hcolumns i)
  have hOL : constrainedOutputs T 2≤L.ker := by
    intro p hp
    have hh : T 2 p=0 := hp.2
    change L p=0
    simpa only [L,T,pairedFrameConstraint_two] using hh
  have hA : ∀ i j,L ((l i).val*(bo j).val)=A i (Pi.single j 1) :=
    fun i j => renamed_private_detector_column f e L₀ (columns i) j
  have hp : (privatePolynomialMap (a := v+v) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector
        (privateGenerator (a := v+v) (s := d-1) ι (fun i => bo.equivFun (l i))))) := by
    simpa only [bo,l,renamedPrivateBasis_column] using hprivate
  obtain ⟨D,hD,hgood⟩ := hv (Fin c → K) T hX hO (hT 4 le_rfl) t c (2*w) bo l hl ι L hOL A hA hp
  exact private_frame_reduction_open_rename (by omega)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) f frame e columns ι L₀ hL₀ D hD hgood

/-- After the scalar threshold, one nonempty frame open works with a fixed
nonzero private tuple; every independent frame in it has a nonempty open of
all its actual prepared coefficients. -/
theorem eventually_counted_small_private_frame_open {d : ℕ}
    (hd : 3≤d) (hd8 : d≤8) (hodd : d%2=1) :
    ∀ᶠ w : ℕ in atTop,4∣2*w →
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
            PrivateReductionOpen (q := upperCount (v+v+z) d) (J := allEvenIndices d)
              (counts := allEvenCount d (2*w) (v+v+z) (err (v+v+z)+extra))
              (privateFrameOutputs frame)
              (privatePowerBiform (a := v+v) (d := d) (fun i => e (columns i)) ι) := by
  obtain ⟨W,hW⟩ := eventually_atTop.mp
    (eventually_quadratic_private_detector_capacity (by omega : 3≤d))
  have hcap : ∀ᶠ w : ℕ in atTop,
      quadraticOutputDimension d (2*w)+(2*(2*w)-1)≤finrank K (Forms K (2*w) 2) := by
    filter_upwards [eventually_ge_atTop W,eventually_gt_atTop 0] with w hw hwpos
    rw [finrank_forms K (2*w) 2 (by omega)]
    simpa only [show 2*w+2-1=2*w+1 by omega] using hW (2*w) (by omega)
  filter_upwards [eventually_counted_small_private_frame_reduction_open (K := K) hd hd8 hodd,
    hcap,eventually_gt_atTop 0] with w hw hcap hwpos
  intro hdiv z extra err herr
  filter_upwards [hw hdiv z extra err herr] with v hv
  intro t ι
  obtain ⟨e,columns,P,hcolumns,hP,hgood⟩ := private_kernel_on_frame_open_nonzero
    (K := K) (a := v+v) (s := d-1) (H := quadraticOutputDimension d (2*w))
    (by omega : 2≤2*w) hcap (by omega) ι
  refine ⟨e,columns,P,hcolumns,hP,?_⟩
  intro frame hframe hframeP
  obtain ⟨L₀,hL₀,hkernel⟩ := hgood frame hframeP
  exact hv t frame hframe e columns hcolumns ι L₀ hL₀ hkernel

end Froberg.PreparedParameters
