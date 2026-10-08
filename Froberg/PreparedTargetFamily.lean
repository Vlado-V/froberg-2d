import Froberg.PreparedParameters
import Quartic.PolynomialRankOpen

/-! A common literal polynomial family for the prepared scalar/even rows,
the outer linear biforms, and the private pure-X generators with fixed lower
parts. The label sum is independent of later reindexing to Fin. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

abbrev OuterSpace (K : Type) [Field K] (σ : Type*) (n d f : ℕ) :=
  Fin f → biformImage (homogeneousSubmodule σ K 1) (Forms K n (d-1))

abbrev Label (q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) :=
  PreparedParameters.Label q J counts ⊕ (Fin f ⊕ Fin u)

abbrev Space (n d q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) :=
  PreparedParameters.Space n d q J counts O × (OuterSpace K σ n d f × (Fin u → Forms K n d))

def variableGenerator : Space n d q f u J counts O →ₗ[K]
    (Label q f u J counts → MvPolynomial (σ ⊕ Fin n) K) where
  toFun p := Sum.elim (PreparedParameters.generator p.1)
    (Sum.elim (fun i => (p.2.1 i).val) (fun i => rename Sum.inr (p.2.2 i).val))
  map_add' p p' := by
    funext i
    rcases i with i | (i | i)
    · rcases i with i | ⟨j,i⟩ <;>
        simp [PreparedParameters.generator,PreparedParameters.scalar,PreparedParameters.high,add_add_add_comm]
    · simp
    · simp
  map_smul' a p := by
    funext i
    rcases i with i | (i | i)
    · rcases i with i | ⟨j,i⟩ <;>
        simp [PreparedParameters.generator,PreparedParameters.scalar,PreparedParameters.high,add_add_add_comm]
    · simp
    · simp

def fixedGenerator (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) :
    Label q f u J counts → MvPolynomial (σ ⊕ Fin n) K :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun i => rename Sum.inl (U i).val+P i))

def generator (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) (p : Space n d q f u J counts O) :
    Label q f u J counts → MvPolynomial (σ ⊕ Fin n) K :=
  variableGenerator p+fixedGenerator U P

@[simp] theorem generator_prepared (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) (p : Space n d q f u J counts O)
    (i : PreparedParameters.Label q J counts) :
    generator U P p (Sum.inl i)=PreparedParameters.generator p.1 i := by
  simp [generator,variableGenerator,fixedGenerator]

@[simp] theorem generator_outer (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) (p : Space n d q f u J counts O) (i : Fin f) :
    generator U P p (Sum.inr (Sum.inl i))=(p.2.1 i).val := by
  simp [generator,variableGenerator,fixedGenerator]

@[simp] theorem generator_private (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) (p : Space n d q f u J counts O) (i : Fin u) :
    generator U P p (Sum.inr (Sum.inr i))=
      rename Sum.inr (p.2.2 i).val+(rename Sum.inl (U i).val+P i) := by
  rfl

theorem generator_homogeneous (hd : 0<d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) (hP : ∀ i,(P i).IsHomogeneous d)
    (p : Space n d q f u J counts O) (i : Label q f u J counts) :
    (generator U P p i).IsHomogeneous d := by
  rcases i with i | (i | i)
  · rw [generator_prepared]
    exact PreparedParameters.generator_homogeneous hO hJ p.1 i
  · rw [generator_outer]
    have hh := biformImage_homogeneous (homogeneousSubmodule σ K 1) (Forms K n (d-1))
      le_rfl le_rfl (p.2.1 i).property
    change (p.2.1 i).val∈homogeneousSubmodule (σ ⊕ Fin n) K d
    simpa only [show 1+(d-1)=d by omega] using hh
  · rw [generator_private]
    exact (p.2.2 i).property.rename_isHomogeneous.add
      ((U i).property.rename_isHomogeneous.add (hP i))

theorem finite_space (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) :
    Module.Finite K (Space n d q f u J counts O) := by
  letI : Module.Finite K (PreparedParameters.Space n d q J counts O) :=
    PreparedParameters.finite_space hO
  letI : Module.Finite K (homogeneousSubmodule (σ ⊕ Fin n) K (1+(d-1))) :=
    Module.Finite.of_basis (finiteVariableFormsBasis _ _)
  letI : Module.Finite K (biformImage (homogeneousSubmodule σ K 1) (Forms K n (d-1))) :=
    Submodule.finiteDimensional_of_le (biformImage_homogeneous _ _ le_rfl le_rfl)
  unfold Space OuterSpace
  infer_instance

theorem generator_polynomial
    [Module.Finite K (Space n d q f u J counts O)]
    (U : Fin u → homogeneousSubmodule σ K d)
    (P : Fin u → MvPolynomial (σ ⊕ Fin n) K) :
    IsPolynomialFamily (fun a : Fin (finrank K (Space n d q f u J counts O)) → K =>
      generator U P ((Module.finBasis K _).equivFun.symm a)) := by
  exact (isPolynomialFamily_linear
    (variableGenerator.comp (Module.finBasis K (Space n d q f u J counts O)).equivFun.symm.toLinearMap)).add
      (isPolynomialFamily_const (fixedGenerator U P))

end Froberg.PreparedTarget
