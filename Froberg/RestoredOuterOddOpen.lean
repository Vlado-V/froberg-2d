module

public import Froberg.RestoredBiformFamily
public import Froberg.ScalarVectorRowsOpen

@[expose] public section

/-! Full odd exactness for the restored even family together with its
outer linear family, on one common parameter open. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q r f t : ℕ} {G : ℝ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

abbrev RestoredOuterSpace (m d q f : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (Poly K h)) :=
  RestoredSpace m d q J counts O × PreparedTarget.OuterSpace K (Fin h) m d f

def restoredOuterVectorParameters (idx : Fin r ≃ Label q J counts) :
    RestoredOuterSpace m d q f J counts O →ₗ[K] ScalarVectorParameters K h m d f r where
  toFun p := (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i),fun i => p.1.1.1 (idx i))
  map_add' p p' := by
    apply Prod.ext
    · funext i
      exact map_add _ _ _
    · rfl
  map_smul' a p := by
    apply Prod.ext
    · funext i
      change PreparedTarget.outerVectorEquiv.symm (a • p.2 i)=
        a • PreparedTarget.outerVectorEquiv.symm (p.2 i)
      exact map_smul (PreparedTarget.outerVectorEquiv (K := K) (h := h) (m := m) (d := d)).symm a (p.2 i)
    · rfl

theorem restoredOuterVectorParameters_surjective (idx : Fin r ≃ Label q J counts) :
    Function.Surjective (restoredOuterVectorParameters (m := m) (d := d) (f := f) (O := O) idx) := by
  rintro ⟨g,Q⟩
  refine ⟨(((fun i => Q (idx.symm i),0),0),fun i => PreparedTarget.outerVectorEquiv (g i)),?_⟩
  apply Prod.ext
  · funext i
    exact LinearEquiv.symm_apply_apply _ _
  · funext i
    exact congrArg Q (idx.symm_apply_apply i)

theorem restored_outer_odd_open (hh : 0<h) (hm : 0 < m) (hd : 3≤d) (hdeven : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (D : MvPolynomial (Fin (finrank K (Fin f → Rows K h m (d-1)))) K)
    (hD : ∃ g : Fin f → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0)
    (hmodel : ∀ g : Fin f → Rows K h m (d-1),eval ((Module.finBasis K _).equivFun g) D≠0 →
      VectorExpansionOpen.StrictModel g d G ∧
      r*finrank K (VectorExpansionOpen.Source g)≤finrank K (VectorExpansionOpen.Target g d))
    (hscalar : HasOddScalarLayersOpen K h m d f r t)
    (hupper : (f+(h+d-1).choose d)*(h+d-1).choose d≤
      (h+(d+1)-1).choose (d+1)*(m+(d-1)-1).choose (d-1)) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ P : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0 →
        OddSplitExact (restoredBiformFamily hdeven hO hJ heven idx slot p.1)
          (fun j => linearOddForm (by omega : 1≤d) (PreparedTarget.outerVectorEquiv.symm (p.2 j))) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  obtain ⟨P,hP,hgood⟩ := scalar_vector_rows_open hh hm (by omega) D hD hmodel hscalar hupper
  obtain ⟨E,hE,hEgood⟩ := principal_open_linear_pullback (restoredOuterVectorParameters (O := O) idx)
    (restoredOuterVectorParameters_surjective idx) P hP _ hgood
  refine ⟨E,hE,?_⟩
  intro p hp
  obtain ⟨hfirst,hhigher⟩ := hEgood p hp
  exact filtered_even_odd_exact hd (restoredBiformFamily hdeven hO hJ heven idx slot p.1)
    (fun i => p.1.1.1 (idx i)) (fun j => PreparedTarget.outerVectorEquiv.symm (p.2 j))
    (restoredBiformFamily_scalar_component (by omega) hdeven hO hJ heven hpos idx slot p.1)
    hfirst hhigher

end Froberg.PreparedParameters
