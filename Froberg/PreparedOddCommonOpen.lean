module

public import Froberg.PreparedCountedOddCycles
public import Froberg.PreparedCountedIndependence
public import Froberg.FiniteBasisPrincipalIntersection
public import Froberg.FullPreparedTargetOpen

@[expose] public section

/-! Independence, full odd exactness, and any further nonempty open
condition hold at one actual prepared parameter. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem exists_prepared_independent_odd_on_open (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (hi : HasIndependentOpen (m := m) (q := q) (f := f) (u := u) (counts := counts) hd hO hJ)
    (ho : HasOddCyclesOpen (m := m) (d := d) (q := q) (f := f) (u := u) (counts := counts) hO) :
    letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
      FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
    ∀ E : MvPolynomial (Fin (finrank K
      (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O))) K,
      (∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) E≠0) →
      ∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
        eval ((Module.finBasis K _).equivFun p) E≠0 ∧
        ∀ U : Fin u → Forms K h d,
          LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U p.1 p.2) ∧ OddCyclesExact U p.1 p.2 := by
  letI : Module.Finite K (FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) :=
    FullPreparedParameters.finite_fixedPureZeroScalarSpace hO
  intro E hE
  obtain ⟨I,hI,higood⟩ := hi
  obtain ⟨D,hD,hdgood⟩ := ho
  let family := ![I,D,E]
  have hex : ∀ j : Fin 3,∃ p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O,
      eval ((Module.finBasis K _).equivFun p) (family j)≠0 := by
    intro j
    fin_cases j
    · exact hI
    · exact hD
    · exact hE
  obtain ⟨p,hp⟩ := finite_basis_principal_intersection family hex
  exact ⟨p,hp 2,fun U => ⟨higood p (hp 0) U,hdgood p (hp 1) U⟩⟩

theorem exists_prepared_odd_upper [CharZero K] {H r : ℕ}
    (hd : 3≤d) (frame : Fin H → Forms K h 2) (U : Fin u → Forms K h d)
    (hi : HasIndependentOpen (m := m) (q := q) (f := f) (u := u)
      (counts := targetLayerCount d h m r) (by omega : 0<d)
      (fun j _ => targetLayerOutput_homogeneous frame j)
      (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le))
    (ho : HasOddCyclesOpen (m := m) (d := d) (q := q) (f := f) (u := u) (J := activeEvenIndices d)
      (counts := targetLayerCount d h m r) (fun j _ => targetLayerOutput_homogeneous frame j))
    (hu : VariablePrivateUpperOpen (m := m) hd f r q frame U) :
    ∃ p : VariablePrivateTargetSpace d m f r q u frame,
      LinearIndependent K (zeroScalarEndpointFamily (by omega : 0<d)
        (fun j _ => targetLayerOutput_homogeneous frame j)
        (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) U p.1 p.2) ∧
      OddCyclesExact U p.1 p.2 ∧
      Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega : 0<d)
        (fun j _ => targetLayerOutput_homogeneous frame j)
        (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) U p.1 p.2)) := by
  obtain ⟨D,hD,hgood⟩ := hu
  obtain ⟨p,hp,hpo⟩ := exists_prepared_independent_odd_on_open (by omega : 0<d)
    (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (activeEvenIndices_bounds hd hj).2.1.le) hi ho D hD
  refine ⟨p,(hpo U).1,(hpo U).2,?_⟩
  rw [zeroScalarEndpointFamily_eq_full]
  exact hgood p hp

end Froberg.PreparedTarget
