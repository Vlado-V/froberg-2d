import Quartic.PolynomialChartGeneric
import Quartic.IteratedCovectorCharts

/-!
# Generic injectivity from the actual prefix-profile charts

All possible integral prefix profiles and coordinate selectors form a finite
family. The charts cover the actual tuple span, and their parameter count is
the literal iterated-block count. No geometric dimension statement is used.
-/

noncomputable section
namespace Quartic.IteratedChartGeneric
open Module MvPolynomial IteratedBlockCharts IteratedCovectorCharts
variable {K : Type*} [Field K] {n q : ℕ} {b : Fin n → ℕ}
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Every possible integral block rank, with its actual ambient upper bound. -/
abbrev Profiles (b : Fin n → ℕ) := (i : Fin n) → Fin (b i+1)

/-- Prefix ranks of an actual subspace in the flattened block coordinates. -/
def profile (S : Submodule K (Fin (∑ i,b i) → K)) : Profiles b :=
  fun i => ⟨finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K)
    (S.comap (coordinates K b).toLinearMap) i), by
      have h := Submodule.finrank_le (FilteredImage.initialPiece (fun i => Fin (b i) → K)
        (S.comap (coordinates K b).toLinearMap) i)
      simp only [Module.finrank_pi, Fintype.card_fin] at h
      omega⟩

/-- Actual tuple spans are covered by the finite polynomial charts of their
own prefix profile, with the exact number of displayed basis vectors. -/
theorem cover_tuple_span (F : Fin q → Fin (∑ i,b i) → K) :
    ∃ j : Selectors b (fun i => (profile (Submodule.span K (Set.range F)) i).val),
      ∃ p : Parameters K j,
        PolynomialSubspaceCovectorCharts.subspace (graphPolynomial j) p=
          Submodule.span K (Set.range F) := by
  exact covered_of_profile _ (fun _ => rfl)

/-- The rank budget is checked against the actual prefix profile of each
nonzero relation tuple. Its finite polynomial chart cover then gives a
nonempty principal open of injective specializations. -/
theorem generic_injective [Infinite K]
    (B : (Fin q → Fin (∑ i,b i) → K) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ F : Fin q → Fin (∑ i,b i) → K,F ≠ 0 →
      let r := fun i => (profile (Submodule.span K (Set.range F)) i).val
      parameterCount b r+q*(∑ i,r i) ≤ finrank K (LinearMap.range (B F))) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ x : V,eval (PolynomialBilinearCoordinates.coordinates K V x) P ≠ 0) ∧
      ∀ x : V,eval (PolynomialBilinearCoordinates.coordinates K V x) P ≠ 0 →
        Function.Injective (B.flip x) := by
  classical
  let C := (r : Profiles b) × Selectors b (fun i => (r i).val)
  let I : C → Type := fun c => ParameterIndex c.2
  let N : C → ℕ := fun c => ∑ i,(c.1 i).val
  let H : ∀ c : C,Fin (N c) → Fin (∑ i,b i) → MvPolynomial (I c) K :=
    fun c => graphPolynomial c.2
  apply PolynomialChartGeneric.generic_injective_actual B H
  intro F hF
  obtain ⟨j,p,hp⟩ := cover_tuple_span F
  refine ⟨⟨profile (Submodule.span K (Set.range F)),j⟩,p,?_,?_⟩
  · intro i
    change F i ∈ PolynomialSubspaceCovectorCharts.subspace (graphPolynomial j) p
    rw [hp]
    exact Submodule.subset_span ⟨i,rfl⟩
  · change Fintype.card (ParameterIndex j)+q*(∑ i,(profile (Submodule.span K (Set.range F)) i).val) ≤ _
    rw [parameter_count]
    exact hbound F hF

section ActualSource
variable {U : Type*} [AddCommGroup U] [Module K U]

/-- The source blocks may be coordinates of an actual finite-dimensional
polynomial quotient, supplied by a checked linear equivalence. -/
theorem generic_injective_of_equiv [Infinite K]
    (e : U ≃ₗ[K] Ambient K b)
    (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ L : Fin q → U,L ≠ 0 →
      let S := (Submodule.span K (Set.range L)).map e.toLinearMap
      let r := fun i => finrank K (FilteredImage.initialPiece (fun i => Fin (b i) → K) S i)
      parameterCount b r+q*finrank K (Submodule.span K (Set.range L)) ≤
        finrank K (LinearMap.range (B L))) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ x : V,eval (PolynomialBilinearCoordinates.coordinates K V x) P ≠ 0) ∧
      ∀ x : V,eval (PolynomialBilinearCoordinates.coordinates K V x) P ≠ 0 →
        Function.Injective (B.flip x) := by
  classical
  let f := e.trans (coordinates K b)
  let T : (Fin q → U) ≃ₗ[K] (Fin q → Fin (∑ i,b i) → K) :=
    LinearEquiv.piCongrRight (fun _ => f)
  let B' := B.comp T.symm.toLinearMap
  have hspan (F : Fin q → Fin (∑ i,b i) → K) :
      (Submodule.span K (Set.range (T.symm F))).map e.toLinearMap=
        (Submodule.span K (Set.range F)).comap (coordinates K b).toLinearMap := by
    apply (Submodule.map_injective_of_injective (coordinates K b).injective)
    rw [Submodule.map_comap_eq_of_surjective (coordinates K b).surjective,
      ←Submodule.map_comp,Submodule.map_span,←Set.range_comp]
    congr 2
    funext i
    exact f.apply_symm_apply (F i)
  have hcount (F : Fin q → Fin (∑ i,b i) → K) :
      finrank K (Submodule.span K (Set.range (T.symm F)))=
        ∑ i,(profile (Submodule.span K (Set.range F)) i).val := by
    have h := finrank_of_profile (Submodule.span K (Set.range F))
      (r := fun i => (profile (Submodule.span K (Set.range F)) i).val) (fun _ => rfl)
    rw [←(e.finrank_map_eq (Submodule.span K (Set.range (T.symm F)))),hspan]
    rw [←(coordinates K b).finrank_map_eq,
      Submodule.map_comap_eq_of_surjective (coordinates K b).surjective]
    exact h
  obtain ⟨P,hP,hgood⟩ := generic_injective B' (by
    intro F hF
    have hL : T.symm F ≠ 0 := by
      intro hz
      apply hF
      exact T.symm.injective (hz.trans T.symm.map_zero.symm)
    have h := hbound (T.symm F) hL
    dsimp only at h ⊢
    rw [hspan,hcount] at h
    exact h)
  refine ⟨P,hP,?_⟩
  intro x hx u v huv
  apply T.injective
  apply hgood x hx
  change B (T.symm (T u)) x=B (T.symm (T v)) x
  change B u x=B v x at huv
  simpa only [LinearEquiv.symm_apply_apply] using huv

end ActualSource
end Quartic.IteratedChartGeneric
