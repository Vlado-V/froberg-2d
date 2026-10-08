import Froberg.MixedHigherRowData

/-! Uniform scalar growth on every concrete higher block. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module Quartic TensorProduct
attribute [local instance] tensorFormGroup

 theorem bilinear_growth_injective_postcompose
    {K P V W Z : Type*} [Field K]
    [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (mu : P →ₗ[K] V →ₗ[K] W) (g : W →ₗ[K] Z) (hg : Function.Injective g)
    (t : ℕ) (hmu : ∀ L : Submodule K V,
      t*finrank K L≤finrank K (BilinearImage.image mu L))
    (L : Submodule K V) :
    t*finrank K L≤finrank K (BilinearImage.image (mu.compr₂ₛₗ g) L) := by
  rw [bilinearImage_postcompose,←(Submodule.equivMapOfInjective g hg _).finrank_eq]
  exact hmu L

variable {K : Type} [Field K] [Infinite K] {h m d q f u b : ℕ}

theorem mixedHigherAction_growth (hd : Odd d) (hd3 : 3≤d)
    (R : Forms K h (1+(d-1)) →ₗ[K] (Fin b → K)) (hR : Function.Surjective R)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (U : Fin u → Forms K h d) (P : Fin u → Forms K h 1 ⊗[K] Forms K m (d-1))
    (hker : R.ker=(Submodule.span K (Set.range U)).map
      (topGrowthDegree (Nat.le_trans (by decide : 1≤3) hd3) h).symm.toLinearMap)
    (t : ℕ)
    (htop : ∀ L : Submodule K (Fin b → K), t*finrank K L≤finrank K
      (BilinearImage.image (projectedTopScalarAction R
        (topGrowthParameters (Nat.le_trans (by decide : 1≤3) hd3) Q F)) L))
    (hmid : ∀ (j : ℕ) (hj : 3≤j) (hjd : j<d), j%2=1 →
      OddScalarLayerProperty t (by omega : 1≤j) (by omega : j≤d)
        (F,fun i => scalarBiformEquiv (h := h) (Q i)))
    (r : MixedHigherIndex d hd3) (L : Submodule K (MixedHigherSource hd hd3 F U P r)) :
    t*finrank K L≤finrank K (BilinearImage.image
      (mixedHigherAction hd hd3 R hR Q F U P hker r) L) := by
  unfold mixedHigherAction
  by_cases ht : 2*r.val.val+1=d
  · rw [dif_pos ht]
    let e := oddHigherTopProjectionEquiv hd hd3 R hR F U P hker r ht
    let mu := topGrowthScalarAction (Nat.le_trans (by decide : 1≤3) hd3) R Q F
    have hg : ∀ S : Submodule K (Fin b → K),
        t*finrank K S≤finrank K (BilinearImage.image mu S) :=
      topGrowthScalarAction_growth _ R hR Q F t htop
    have hge := fun S => bilinear_growth_source_equiv mu e t hg S
    have hh := bilinear_growth_injective_postcompose (mu.compl₂ e.toLinearMap)
      (LinearMap.inl K (MixedTopTarget hd3 R Q F) (MixedMiddleTarget hd3 Q F r))
      (fun x y hxy => congrArg Prod.fst hxy) t hge L
    exact hh
  · rw [dif_neg ht]
    let e := oddHigherNonTopQuotientEquiv hd hd3 F U P r ht
    let mu := oddActualRowScalarAction (b := 2*r.val.val+1) (by omega)
      (by have := r.val.isLt; omega) Q F
    have hg : ∀ S : Submodule K (OddHigherBlock K h m d
        (Nat.le_trans (by decide : 1≤3) hd3) r),
        t*finrank K S≤finrank K (BilinearImage.image mu S) :=
      oddActualRowScalarAction_growth _ _ Q F t
        (hmid (2*r.val.val+1) (mixedHigherIndex_ge_three hd3 r)
          (by have := r.val.isLt; omega) (by omega))
    have hge := fun S => bilinear_growth_source_equiv mu e t hg S
    have hh := bilinear_growth_injective_postcompose (mu.compl₂ e.toLinearMap)
      (LinearMap.inr K (MixedTopTarget hd3 R Q F) (MixedMiddleTarget hd3 Q F r))
      (fun x y hxy => congrArg Prod.snd hxy) t hge L
    exact hh

end Froberg
