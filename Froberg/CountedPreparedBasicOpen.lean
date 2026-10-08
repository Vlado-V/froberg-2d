import Froberg.CountedUpperFrames
import Froberg.CountedAllEvenCertificates
import Froberg.PreparedOddCertificateOpen

/-! A single open on the actual prepared parameter space gives linear
independence, odd exactness and the upper-target surjection. The quadratic
frame can be chosen together with any further nonempty frame open. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial PreparedParameters
open scoped Topology
variable {K : Type} [Field K] [CharZero K]

def BasicCertificate {h m d q f u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (Poly K h)} (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) : Prop :=
  LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U p.1 p.2) ∧
    OddCyclesExact U p.1 p.2 ∧
    Function.Surjective (upperTargetMap (zeroScalarEndpointFamily hd hO hJ U p.1 p.2))

def HasBasicOpen {h m d q f u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {O : ℕ → Submodule K (Poly K h)} (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → Forms K h d) : Prop :=
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  ∃ D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
    (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 → BasicCertificate hd hO hJ U p

theorem HasUpperWitness.all_even_basic_open {h m d H f r q u : ℕ}
    (hd : 3 ≤ d) (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (hi : HasIndependentOpen (m := m) (q := q) (f := f) (u := u)
      (counts := allEvenCount d h m r) (by omega : 0<d)
      (fun j _ => targetLayerOutput_homogeneous frame j)
      (fun j hj => (mem_allEvenIndices.mp hj).2.1))
    (ho : HasOddCyclesOpen (m := m) (d := d) (q := q) (f := f) (u := u)
      (counts := allEvenCount d h m r)
      (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j))
    (hw : HasUpperWitness (m := m) d f r q frame U (fun _ => 0)) :
    HasBasicOpen (m := m) (q := q) (f := f) (counts := allEvenCount d h m r)
      (by omega : 0<d) (fun j _ => targetLayerOutput_homogeneous frame j)
      (fun j hj => (mem_allEvenIndices.mp hj).2.1) U := by
  obtain ⟨D,hD,hupper⟩ := hw.all_even_variable_private_open hd frame U 0
  obtain ⟨E,hE,hgood⟩ := exists_prepared_independent_odd_certificate_open (by omega)
    (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) hi ho D hD
  refine ⟨E,hE,?_⟩
  intro p hp
  obtain ⟨hD',hcert⟩ := hgood p hp
  exact ⟨(hcert U).1,(hcert U).2,hupper p hD'⟩

theorem eventually_counted_basic_frames {d : ℕ} (hd : 3 ≤ d) (hdodd : d%2=1) :
    ∀ᶠ h : ℕ in atTop,∀ (k lo : ℕ),0<k → h=k*centralHalfBinomial d → 0<h →
      ∀ (upper : Bool) (a f e : ℕ → ℕ),(∀ n,a n≤n) →
      (∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) →
      ∀ δ : ℝ,0<δ →
      (∀ᶠ n : ℕ in atTop,δ*(n : ℝ)^(2*d-2)<dimensionReserve d h n (f n)) →
      ∀ (u extra : ℕ),∀ᶠ n : ℕ in atTop,
        ∃ D : MvPolynomial (Fin (finrank K (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x D≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) D≠0 →
            LinearIndependent K frame ∧
            ∀ U : Fin u → Forms K h d,PureFamilyAdmissible U →
              HasBasicOpen (m := n) (q := upperCount n d) (f := f n)
                (counts := allEvenCount d h n (e n+extra)) (by omega : 0<d)
                (fun j _ => targetLayerOutput_homogeneous frame j)
                (fun j hj => (mem_allEvenIndices.mp hj).2.1) U := by
  filter_upwards [eventually_indexed_upper_frames (K := K) hd] with h hh
  intro k lo hk hkh hhpos upper a f e ha hc δ hδ hres u extra
  have hi := exact_counts_all_even_independent_open (K := K) (u := u) hd hhpos upper a f e hc extra
  have ho := exact_counts_all_even_odd_open (K := K) (u := u) hd hdodd hk hkh hhpos
    upper a f e ha hc hδ hres extra
  have hupper := hh f (exact_conditions_outer_limit hd upper a f e hc)
  filter_upwards [hi,ho,hupper,hc] with n hnI hnO hnU hnC
  obtain ⟨D,hD,hframe⟩ := hnU (e n+extra) (hnC.quadratic_lower.trans (by exact_mod_cast Nat.le_add_right (e n) extra))
  refine ⟨D,hD,?_⟩
  intro frame hf
  obtain ⟨hfi,hfw⟩ := hframe frame hf
  refine ⟨hfi,fun U hU => ?_⟩
  exact (hfw u (upperCount n d) U hU).all_even_basic_open hd frame U
    (hnI _ _) (hnO _ _)

end Froberg.PreparedTarget
