module

public import Froberg.AllEvenUpperOpen
public import Froberg.PreparedPureFamilyCore
public import Froberg.PreparedOddCertificateOpen

@[expose] public section

/-! Finite certificate data, independent of the legacy eventual construction. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Filter Module MvPolynomial PreparedParameters
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

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


end Froberg.PreparedTarget
