module

public import Froberg.BiformTensorFamily
public import Froberg.SurjectiveParameterOpen

@[expose] public section

/-! A finite collection of target rows is simultaneously filled by one
family in each generator layer. Rows may reuse the same layer. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
variable {K : Type*} [Field K] [Infinite K]
variable {J B : Type*} [Fintype J] [Fintype B] [DecidableEq J]
variable {h m : ℕ}
attribute [local instance] tensorGroup

abbrev BiformLayerFamily (K : Type*) [Field K] (h m : ℕ) (j e r : J → ℕ) :=
  (a : J) → Fin (r a) → Forms K h (j a) ⊗[K] Forms K m (e a)

theorem biform_layers_common_open (j e r : J → ℕ) (layer : B → J) (x y : B → ℕ)
    (hwit : ∀ b,∃ g : Fin (r (layer b)) → Forms K h (j (layer b)) ⊗[K] Forms K m (e (layer b)),
      Function.Surjective (biformTensorFamilyMap (x := x b) (y := y b) g)) :
    ∃ D : MvPolynomial (Fin (finrank K (BiformLayerFamily K h m j e r))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → ∀ b,
        Function.Surjective (biformTensorFamilyMap (x := x b) (y := y b)
          (((Module.finBasis K (BiformLayerFamily K h m j e r)).equivFun.symm a) (layer b))) := by
  let decode := (Module.finBasis K (BiformLayerFamily K h m j e r)).equivFun.symm.toLinearMap
  apply surjective_polynomial_common_open
    (fun b a => biformTensorFamilyMap (x := x b) (y := y b) (decode a (layer b)))
  · intro b
    exact isPolynomialFamily_linear
      ((biformTensorFamilyMap (x := x b) (y := y b)).comp
        ((LinearMap.proj (layer b)).comp decode))
  · intro b
    obtain ⟨g,hg⟩ := hwit b
    refine ⟨(Module.finBasis K _).equivFun (Pi.single (layer b) g),?_⟩
    simpa only [decode,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Pi.single_eq_same] using hg

/-- Each witness may start as a pure convolution family. The common family
is allowed to be an arbitrary biform, exactly as in the prepared parameters. -/
theorem biform_layers_common_open_of_pure (j e r : J → ℕ) (layer : B → J) (x y : B → ℕ)
    (hwit : ∀ b,∃ (o : Fin (r (layer b)) → Forms K h (j (layer b)))
      (f : Fin (r (layer b)) → Forms K m (e (layer b))),
      Function.Surjective (biformFamilyMap (x := x b) (y := y b) o f)) :
    ∃ D : MvPolynomial (Fin (finrank K (BiformLayerFamily K h m j e r))) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → ∀ b,
        Function.Surjective (biformTensorFamilyMap (x := x b) (y := y b)
          (((Module.finBasis K (BiformLayerFamily K h m j e r)).equivFun.symm a) (layer b))) := by
  apply biform_layers_common_open j e r layer x y
  intro b
  obtain ⟨o,f,hof⟩ := hwit b
  exact ⟨fun i => o i ⊗ₜ[K] f i,by simpa only [biformTensorFamilyMap_pure] using hof⟩

end Froberg
