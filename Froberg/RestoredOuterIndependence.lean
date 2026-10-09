module

public import Froberg.BiformSplitIndependence
public import Froberg.RestoredOuterOddOpen

@[expose] public section

/-! Full restored endpoint independence holds on the same actual affine
space as the restored odd-row and pure-basis conditions. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def restoredOuterEndpoint (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) : Fin (r+f) → Forms K (h+m) d :=
  biformSplitEndpoint (restoredBiformFamily hd hO hJ heven idx slot p.1)
    (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i)))

theorem restored_outer_independent (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O)
    (hscalar : LinearIndependent K (fun i => p.1.1.1 (idx i)))
    (hlinear : LinearIndependent K (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))) :
    LinearIndependent K (restoredOuterEndpoint hdp hd hO hJ heven idx slot p) := by
  have hs : LinearIndependent K (fun i => rename (Sum.inr : Fin m → Fin h ⊕ Fin m) (p.1.1.1 (idx i)).val) := by
    apply (hscalar.map' (Forms K m d).subtype (Submodule.ker_subtype _)).map'
      (rename Sum.inr).toLinearMap
    exact LinearMap.ker_eq_bot.mpr (rename_injective _ Sum.inr_injective)
  apply biformSplitEndpoint_independent
  · simpa only [restoredBiformFamily_scalar_component (by omega) hd hO hJ heven hpos idx slot] using hs
  · simpa only [linearOddForm_component,ite_true] using linearOddForm_independent hdp _ hlinear
  · intro i
    rw [linearOddForm_component,if_neg (by decide)]

def HasRestoredIndependentOpen (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r) : Prop :=
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  ∃ P : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
    (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
    ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0 →
      LinearIndependent K (restoredOuterEndpoint hdp hd hO hJ heven idx slot p)

theorem restored_outer_independent_open (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hq : r≤finrank K (Forms K m d)) (hf : f≤finrank K (Rows K h m (d-1))) :
    HasRestoredIndependentOpen (m := m) (f := f) hdp hd hO hJ heven idx slot := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  obtain ⟨P,hP,hgood⟩ := scalar_vector_independence_open hq hf
  obtain ⟨E,hE,hEgood⟩ := principal_open_linear_pullback (restoredOuterVectorParameters (O := O) idx)
    (restoredOuterVectorParameters_surjective idx) P hP _ hgood
  refine ⟨E,hE,?_⟩
  intro p hp
  obtain ⟨hg,hq⟩ := hEgood p hp
  exact restored_outer_independent hdp hd hO hJ heven hpos idx slot p hq hg

end Froberg.PreparedParameters
