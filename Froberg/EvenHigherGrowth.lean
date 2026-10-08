import Froberg.EvenBackgroundScalar
import Froberg.MixedHigherGrowth
import Froberg.OddAmbientBottomRepresentatives

/-! All higher source rows in the even case act independently on actual
Q,F quotient target rows, while every unused target row is retained. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f : ℕ}
variable (hd3 : 3≤d)
  (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
local notation "hdp" => Nat.le_trans (by decide : 1≤3) hd3
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "hQ₀" => fun i => scalarEvenBiform_weighted (h := h) (Q i)
local notation "hF₁" => fun i => oddLinearBiform_weighted hdp (F i)
local notation "eW" => oddTargetBaseEquiv hdp Q₀ F₁ hQ₀ hF₁
local notation "eV" => oddSourceBaseEquiv hdp F
local notation "μ" => evenBackgroundScalar hdp Q F

def evenHigherProjection (r : MixedHigherIndex d hd3) :
    EvenBackgroundTarget hdp Q F →ₗ[K] MixedMiddleTarget hd3 Q F r :=
  oddBackgroundRowProjection (by omega) (by have := r.val.isLt; omega) (by omega)
    (fun i => scalarBiformEquiv (h := h) (Q i)) F

theorem evenHigherProjection_scalar (p : Forms K m d)
    (v : EvenBackgroundSource hdp F) (r : MixedHigherIndex d hd3) :
    evenHigherProjection hd3 Q F r (μ p v)=
      oddActualRowScalarAction (by omega) (by have := r.val.isLt; omega) Q F p ((eV v).2 r) := by
  obtain ⟨v,rfl⟩ := (Submodule.span K (Set.range F₁)).mkQ_surjective v
  change oddBackgroundRowProjection _ _ _ _ _
    (evenBackgroundScalar hdp Q F p ((Submodule.span K (Set.range F₁)).mkQ v))=_
  have hh := evenBackgroundScalar_higher_projection hdp (by omega : 1≤2*r.val.val+1)
    (by have := r.val.isLt; omega : 2*r.val.val+1≤d) (by omega) Q F p v
  refine hh.trans ?_
  congr 1
  change biformTensorComponent (by have := r.val.isLt; omega : 2*r.val.val+1≤d) v=
    oddBiformCoordinatesEquiv v r.val
  exact biformTensorComponent_eq_oddCoordinates v r.val

theorem evenHigherProjection_kills_bottom (r : MixedHigherIndex d hd3)
    (x : OddTargetRowQuotient Q₀ F₁ (oddTargetBottomIndex hdp)) :
    evenHigherProjection hd3 Q F r ((eW).symm (x,0))=0 := by
  obtain ⟨v,hv,hx⟩ := exists_odd_target_bottom_representative hdp Q₀ F₁ hQ₀ hF₁ x
  have he : (eW).symm (x,0)=(oddBackgroundRelations Q₀ F₁).mkQ v := by
    apply (eW).injective
    rw [LinearEquiv.apply_symm_apply]
    change (x,0)=oddTargetBaseMap hdp Q₀ F₁ hQ₀ hF₁ v
    apply Prod.ext
    · exact hx.symm
    · exact (oddTargetBaseMap_weighted_higher_zero hdp Q₀ F₁ hQ₀ hF₁ v hv).symm
  rw [he]
  change oddBackgroundRowProjection _ _ _ _ _ ((oddBackgroundRelations Q₀ F₁).mkQ v)=0
  change (tensorOddRowRelations (b := 2*r.val.val+1) (by omega)
    (by have := r.val.isLt; omega) (fun i => scalarBiformEquiv (h := h) (Q i)) F).mkQ
      (biformTensorComponent (by have := r.val.isLt; omega) v)=0
  rw [biformTensorComponent_weight_ne _ v hv (by
    have := mixedHigherIndex_ge_three hd3 r
    omega),map_zero]

theorem evenAmbientHigher_growth
    (t : ℕ)
    (hmid : ∀ (j : ℕ) (hj : 3≤j) (hjd : j≤d), j%2=1 →
      OddScalarLayerProperty t (by omega : 1≤j) hjd
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (L : Submodule K (EvenBackgroundSource hdp F)) :
    t*(finrank K L-finrank K (L.comap
      ((eV).symm.toLinearMap.comp (LinearMap.inl K (OddBottomQuotient F)
        (HigherOddCoordinates K h m d hdp)))))≤
      finrank K (BilinearImage.image (splitTargetHigherAction eW μ) L) := by
  let pi := LinearMap.pi (fun r : MixedHigherIndex d hd3 =>
    splitHigherProjection eW (evenHigherProjection hd3 Q F r))
  let diag := fun r : MixedHigherIndex d hd3 => oddActualRowScalarAction
    (b := 2*r.val.val+1) (by omega) (by have := r.val.isLt; omega) Q F
  apply higher_growth_of_pi_projection eV pi (splitTargetHigherAction eW μ) diag
  · intro p v r
    change splitHigherProjection eW (evenHigherProjection hd3 Q F r)
      (splitTargetHigherAction eW μ p v)=_
    rw [splitHigherProjection_action eW _ (evenHigherProjection_kills_bottom hd3 Q F r)]
    exact evenHigherProjection_scalar hd3 Q F p v r
  · intro r S
    exact oddActualRowScalarAction_growth _ _ Q F t
      (hmid (2*r.val.val+1) (mixedHigherIndex_ge_three hd3 r) (by have := r.val.isLt; omega)
        (by omega)) S

end Froberg
