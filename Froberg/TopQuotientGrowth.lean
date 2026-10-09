module

public import Froberg.ProjectedTopAugmentation
public import Froberg.TopTensorExactness
public import Froberg.TensorFamilyGrowth

@[expose] public section

/-! The scalar-growth bound is a statement about the literal tensor quotient
of the manuscript, with both the pure and mixed relation spaces present. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct Quartic Quartic.SplitTensor MvPolynomial
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K] {h m e b qF qS t : ℕ}

theorem projectedTopMap_eq_tensorFamily (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (p : ProjectedTopParameters K h m e qF qS) :
    projectedTopMap P p=projectedTensorFamily (K := K) (A := Fin qF → Forms K h e ⊗[K] Forms K m 1) P (rawTopFamily p.1) p.2 := by
  have hQ : BilinearScalarFamily.multiplication (K := K)
      (F := Forms K m (1+e)) (V := Fin b → K) (W := (Fin b → K) ⊗[K] Forms K m (1+e))
      (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e))) p.2=
      sumTensorRight (K := K) (X := Fin b → K) p.2 := by
    apply LinearMap.ext
    intro x
    simp only [BilinearScalarFamily.multiplication_apply,sumTensorRight_apply]
    rfl
  simp only [projectedTopMap,twoFamilyMultiplication,projectedTopFamily_eq,hQ,
    projectedTensorFamily]

theorem top_tensor_scalar_growth (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : Function.Surjective P) (p : ProjectedTopParameters K h m e qF qS)
    (hgrowth : ∀ L : Submodule K (Fin b → K),
      t*finrank K L≤finrank K (BilinearImage.image (projectedTopScalarAction P p) L))
    (L : Submodule K (Fin b → K)) :
    t*finrank K L≤finrank K (BilinearImage.image
      (tensorFamilyScalarAction (K := K) (A := Fin qF → Forms K h e ⊗[K] Forms K m 1) P hP (rawTopFamily p.1) p.2) L) := by
  apply tensorFamily_scalar_growth (K := K)
    (A := Fin qF → Forms K h e ⊗[K] Forms K m 1) P hP (rawTopFamily p.1) p.2 t _ L
  intro M
  have hg := hgrowth M
  change t*finrank K M≤finrank K (BilinearImage.image
    (scalarModulo (K := K)
      (U := (Fin qF → Forms K h e ⊗[K] Forms K m 1) × (Fin qS → Fin b → K))
      (V := Fin b → K) (W := (Fin b → K) ⊗[K] Forms K m (1+e))
      (P := Forms K m (1+e)) (projectedTopMap P p)
      (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e)))) M) at hg
  rw [projectedTopMap_eq_tensorFamily] at hg
  exact hg

theorem top_tensor_growth_open (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : Function.Surjective P) (hopen : ProjectedTopGrowthOpen P m qF qS t) :
    ∃ D : MvPolynomial (Fin (finrank K (ProjectedTopParameters K h m e qF qS))) K,
      (∃ p : ProjectedTopParameters K h m e qF qS,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : ProjectedTopParameters K h m e qF qS,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (projectedTopMap P p) ∧
        Disjoint (rawTopFamily p.1).range
          (leftRelations P.ker ⊔ rightRelations (Submodule.span K (Set.range p.2))) ∧
        ∀ L : Submodule K (Fin b → K),
          t*finrank K L≤finrank K (BilinearImage.image
            (tensorFamilyScalarAction (K := K) (A := Fin qF → Forms K h e ⊗[K] Forms K m 1) P hP (rawTopFamily p.1) p.2) L) := by
  obtain ⟨D,hD,hgood⟩ := hopen
  refine ⟨D,hD,?_⟩
  intro p hp
  obtain ⟨hi,hg⟩ := hgood p hp
  exact ⟨hi,top_tensor_separation P p.1 p.2 hi,top_tensor_scalar_growth P hP p hg⟩

end Froberg
