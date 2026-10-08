import Froberg.PreparedJointSelection
import Froberg.PreparedOddCertificateOpen

/-! The generic child flag and all supplied odd prepared certificates can
be chosen before the final positive-scalar fiber is fixed. -/
noncomputable section
set_option maxHeartbeats 100000
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial VectorExpansionOpen
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

/-- The outer family and the base scalar family are fixed on this fiber,
so its strict model and child flag agree with those at the selected point. -/
theorem prepared_joint_positive_scalar_fiber_at {h m d q f u : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
    (hO : ∀ j ∈ J, O j ≤ Forms K h j) (G C : ℝ) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ (D : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K)
      (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O),
      eval ((Module.finBasis K _).equivFun p) D ≠ 0 →
      StrictModel (fun i => outerVectorEquiv.symm (p.2.2 i)) d G →
      ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2.2 i)) d)
        (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) C
        (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i))) →
      ∃ E : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) m d J counts))) K,
        eval ((Module.finBasis K _).equivFun (fullScalarFiberCoordinates p).1) E ≠ 0 ∧
        ∀ a, eval ((Module.finBasis K _).equivFun a) E ≠ 0 →
          let p' := fullScalarFiberCoordinates.symm (a,(fullScalarFiberCoordinates p).2)
          eval ((Module.finBasis K _).equivFun p') D ≠ 0 ∧
          StrictModel (fun i => outerVectorEquiv.symm (p'.2.2 i)) d G ∧
          ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p'.2.2 i)) d)
            (outerScalarDeficit (fun i => outerVectorEquiv.symm (p'.2.2 i))) C
            (coefficientCoordinates (fun i => p'.2.1.1 (Sum.inl i))) := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D p hp hmodel hchild
  obtain ⟨E,hE,hgood⟩ := principal_open_positive_scalar_fiber_at hO D p hp
  exact ⟨E,hE,fun a ha => ⟨hgood a ha,hmodel,hchild⟩⟩

/-- Literal independence and odd-cycle exactness, uniformly in the pure
top forms, together with the actual strict model and generic child flag. -/
def PreparedGenericCertificate {h m d q f u : ℕ}
    {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}
    (hd : 0 < d) (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d)
    (G C : ℝ) (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) : Prop :=
  (∀ U : Fin u → Forms K h d,
    LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U p.1 p.2) ∧
      OddCyclesExact U p.1 p.2) ∧
    StrictModel (fun i => outerVectorEquiv.symm (p.2.2 i)) d G ∧
    ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2.2 i)) d)
      (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) C
      (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i)))

/-- Select the full prepared parameter inside all certificate opens and
the supplied open before freezing every coordinate except positive scalars. -/
theorem exact_counts_prepared_certified_fiber {d k h lo u : ℕ}
    (hd : 3 ≤ d) (hk : 0 < k) (hh : h = k*centralHalfBinomial d) (hhpos : 0 < h)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n, a n ≤ n)
    (hc : ∀ᶠ n in atTop, ExactCountConditions d k h lo n (a n) (f n) (e n) upper)
    {δ : ℝ} (hδ : 0 < δ)
    (hreserve : ∀ᶠ n : ℕ in atTop, δ*(n : ℝ)^(2*d-2) < dimensionReserve d h n (f n)) :
    ∃ G C : ℝ, 0 < G ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d),
      HasIndependentOpen (m := n) (q := upperCount n d) (f := f n) (u := u)
        (counts := counts) (by omega : 0 < d) hO hJ →
      HasOddCyclesOpen (m := n) (d := d) (q := upperCount n d) (f := f n) (u := u)
        (counts := counts) hO →
      letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
        FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
      ∀ D : MvPolynomial (Fin (finrank K
        (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O))) K,
        (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O,
          eval ((Module.finBasis K _).equivFun p) D ≠ 0) →
        ∃ (rest : FullScalarFiberRest n d (upperCount n d) (f n) u J counts O)
          (A : MvPolynomial (Fin (finrank K (PositiveScalars (K := K) n d J counts))) K),
          (∃ a₀ : PositiveScalars (K := K) n d J counts,
            eval ((Module.finBasis K _).equivFun a₀) A ≠ 0) ∧
          ∀ a', eval ((Module.finBasis K _).equivFun a') A ≠ 0 →
            let p := fullScalarFiberCoordinates.symm (a',rest)
            eval ((Module.finBasis K _).equivFun p) D ≠ 0 ∧
            PreparedGenericCertificate (by omega : 0 < d) hO hJ
              (G*(n : ℝ)^d) (C*(n : ℝ)^d) p := by
  obtain ⟨G,C,hG,hC,hjoint⟩ := exact_counts_prepared_joint (K := K) (u := u)
    hd hk hh hhpos upper a f e ha hc hδ hreserve
  refine ⟨G,C,hG,hC,?_⟩
  filter_upwards [hjoint] with n hn
  intro J counts O hO hJ hi ho
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace n d (upperCount n d) (f n) u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro D hD
  obtain ⟨E,hE,hcert⟩ := exists_prepared_independent_odd_certificate_open
    (by omega : 0 < d) hO hJ hi ho D hD
  obtain ⟨p,hp,hmodel,hchild⟩ := hn J counts O hO E hE
  obtain ⟨A,hA,hgood⟩ := prepared_joint_positive_scalar_fiber_at hO
    (G*(n : ℝ)^d) (C*(n : ℝ)^d) E p hp hmodel hchild
  refine ⟨(fullScalarFiberCoordinates p).2,A,⟨(fullScalarFiberCoordinates p).1,hA⟩,?_⟩
  intro a' ha'
  obtain ⟨hE',hm,hc'⟩ := hgood a' ha'
  obtain ⟨hD',hodd⟩ := hcert _ hE'
  exact ⟨hD',hodd,hm,hc'⟩

end Froberg.PreparedParameters
