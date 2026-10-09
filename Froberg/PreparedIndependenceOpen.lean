module

public import Froberg.PreparedFamilyIndependence
public import Froberg.ScalarVectorIndependenceOpen

@[expose] public section

/-! A nonempty principal open makes the full prepared family independent.
The same open works for every choice of the pure top forms. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem combined_linear_independent (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f)
    (hg : LinearIndependent K (combinedVectorEnumeration P F)) :
    LinearIndependent K (combinedLinear P F) := by
  have h₁ := hg.map' (outerVectorEquiv (K := K) (h := h) (m := m) (d := d)).toLinearMap
    (LinearMap.ker_eq_bot.mpr outerVectorEquiv.injective)
  have h₂ := h₁.map' (biformImage (Forms K h 1) (Forms K m (d-1))).subtype
    (Submodule.ker_subtype _)
  have h₃ := h₂.comp finSumFinEquiv finSumFinEquiv.injective
  change LinearIndependent K (fun i : Fin f ⊕ Fin u =>
    sumBiformMap (linearOutputTensorEquiv (combinedVectorEnumeration P F (finSumFinEquiv i)))) at h₃
  simpa only [combinedVectorEnumeration_val,Equiv.symm_apply_apply] using h₃

def HasIndependentOpen (hd : 0<d) (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) : Prop :=
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  ∃ P : MvPolynomial (Fin (finrank K
    (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
    (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) P≠0) ∧
    ∀ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) P≠0 →
      ∀ U : Fin u → Forms K h d,LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U p.1 p.2)

theorem prepared_independent_open (hd : 1<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j)
    (hq : Fintype.card (PreparedParameters.Label q J counts)≤finrank K (Forms K m d))
    (hf : f+u≤finrank K (Rows K h m (d-1))) :
    HasIndependentOpen (m := m) (q := q) (f := f) (u := u) (counts := counts) (by omega) hO hJ := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  obtain ⟨P,hP,hgood⟩ := scalar_vector_independence_open hq hf
  obtain ⟨E,hE,hEgood⟩ := principal_open_linear_pullback
    (preparedOddVectorParameters (K := K) (h := h) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) preparedOddVectorParameters_surjective P hP _ hgood
  refine ⟨E,hE,?_⟩
  intro p hp U
  obtain ⟨hg,hq⟩ := hEgood p hp
  apply prepared_family_independent hd hO hJ hpos U p.1 p.2
  · have hh := hq.comp (Fintype.equivFin (PreparedParameters.Label q J counts)) (Equiv.injective _)
    simpa only [preparedOddVectorParameters,LinearMap.coe_mk,AddHom.coe_mk,
      scalarEnumeration,Function.comp_def,Equiv.symm_apply_apply] using hh
  · exact combined_linear_independent p.1 p.2.2 hg

end Froberg.PreparedTarget
