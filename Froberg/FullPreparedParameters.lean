import Froberg.PreparedTargetRestrictions

/-! The common affine parameter space lets the pure private forms, their
linear biform parts, and all prepared rows vary together. Fixed-fiber
witnesses are points of this space; their certificates are not extended
to other fibers without applying rank openness to this full family. -/
noncomputable section
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

abbrev Space (m d q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) :=
  (Fin u → homogeneousSubmodule σ K d) ×
    (PreparedTarget.OuterSpace K σ m d u × PreparedTarget.Space m d q f u J counts O)

abbrev ZeroScalarSpace (m d q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (O : ℕ → Submodule K (MvPolynomial σ K)) :=
  (Fin u → homogeneousSubmodule σ K d) ×
    (PreparedTarget.OuterSpace K σ m d u ×
      (PreparedParameters.Space m d q J counts O × PreparedTarget.OuterSpace K σ m d f))

def generator : Space m d q f u J counts O →ₗ[K]
    (PreparedTarget.Label q f u J counts → MvPolynomial (σ ⊕ Fin m) K) where
  toFun p := PreparedTarget.generator p.1 (fun i => (p.2.1 i).val) p.2.2
  map_add' p p' := by
    funext i
    simp only [PreparedTarget.generator, Prod.fst_add, Prod.snd_add,
      map_add, Pi.add_apply]
    rcases i with i | (i | i)
    · simp only [PreparedTarget.fixedGenerator,Sum.elim_inl,add_zero]
    · simp only [PreparedTarget.fixedGenerator,Sum.elim_inr,Sum.elim_inl,add_zero]
    · simp only [PreparedTarget.fixedGenerator,Sum.elim_inr,Pi.add_apply,
        Submodule.coe_add,map_add]
      abel
  map_smul' a p := by
    funext i
    change PreparedTarget.variableGenerator (a • p.2.2) i+
        PreparedTarget.fixedGenerator (a • p.1) (fun j => a • (p.2.1 j).val) i =
      a • (PreparedTarget.variableGenerator p.2.2 i+
        PreparedTarget.fixedGenerator p.1 (fun j => (p.2.1 j).val) i)
    rw [map_smul]
    rcases i with i | (i | i) <;>
      simp [PreparedTarget.fixedGenerator,smul_add]

@[simp] theorem generator_apply (p : Space m d q f u J counts O)
    (i : PreparedTarget.Label q f u J counts) :
    generator p i=PreparedTarget.generator p.1 (fun i => (p.2.1 i).val) p.2.2 i := rfl

theorem private_homogeneous (hd : 0 < d)
    (P : PreparedTarget.OuterSpace K σ m d u) (i : Fin u) :
    (P i).val.IsHomogeneous d := by
  have hp := biformImage_homogeneous (homogeneousSubmodule σ K 1)
    (Forms K m (d-1)) le_rfl le_rfl (P i).property
  change (P i).val∈homogeneousSubmodule (σ ⊕ Fin m) K d
  simpa only [show 1+(d-1)=d by omega] using hp

theorem generator_homogeneous (hd : 0 < d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (p : Space m d q f u J counts O) (i : PreparedTarget.Label q f u J counts) :
    (generator p i).IsHomogeneous d :=
  PreparedTarget.generator_homogeneous hd hO hJ p.1 (fun i => (p.2.1 i).val)
    (private_homogeneous hd p.2.1) p.2.2 i

def forms (hd : 0 < d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d) :
    Space m d q f u J counts O →ₗ[K]
      (PreparedTarget.Label q f u J counts → homogeneousSubmodule (σ ⊕ Fin m) K d) where
  toFun p i := ⟨generator p i,generator_homogeneous hd hO hJ p i⟩
  map_add' p p' := by
    funext i
    apply Subtype.ext
    exact congrFun (map_add generator p p') i
  map_smul' a p := by
    funext i
    apply Subtype.ext
    exact congrFun (map_smul generator a p) i

@[simp] theorem forms_val (hd : 0 < d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (p : Space m d q f u J counts O) (i : PreparedTarget.Label q f u J counts) :
    (forms hd hO hJ p i).val=generator p i := rfl

theorem forms_eq_fixed (hd : 0 < d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d)
    (p : Space m d q f u J counts O) :
    forms hd hO hJ p=PreparedTarget.forms hd hO hJ p.1 (fun i => (p.2.1 i).val)
      (private_homogeneous hd p.2.1) p.2.2 := rfl

theorem finite_space (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) :
    Module.Finite K (Space m d q f u J counts O) := by
  letI : Module.Finite K (PreparedTarget.Space m d q f u J counts O) :=
    PreparedTarget.finite_space hO
  letI : Module.Finite K (homogeneousSubmodule σ K d) :=
    Module.Finite.of_basis (finiteVariableFormsBasis _ _)
  letI : Module.Finite K (homogeneousSubmodule (σ ⊕ Fin m) K (1+(d-1))) :=
    Module.Finite.of_basis (finiteVariableFormsBasis _ _)
  letI : Module.Finite K (biformImage (homogeneousSubmodule σ K 1) (Forms K m (d-1))) :=
    Submodule.finiteDimensional_of_le (biformImage_homogeneous _ _ le_rfl le_rfl)
  unfold Space PreparedTarget.OuterSpace
  infer_instance

def zeroPrivateScalar : ZeroScalarSpace m d q f u J counts O →ₗ[K]
    Space m d q f u J counts O where
  toFun p := (p.1,(p.2.1,PreparedTarget.zeroPrivateScalar p.2.2))
  map_add' p p' := by simp
  map_smul' a p := by simp

theorem zeroPrivateScalar_injective : Function.Injective
    (zeroPrivateScalar (K := K) (m := m) (d := d) (q := q) (f := f) (u := u)
      (J := J) (counts := counts) (O := O)) := by
  intro p p' he
  apply Prod.ext
  · exact congrArg (fun x : Space m d q f u J counts O => x.1) he
  apply Prod.ext
  · exact congrArg (fun x : Space m d q f u J counts O => x.2.1) he
  apply Prod.ext
  · exact congrArg (fun x : Space m d q f u J counts O => x.2.2.1) he
  · exact congrArg (fun x : Space m d q f u J counts O => x.2.2.2.1) he

theorem finite_zeroScalarSpace (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) :
    Module.Finite K (ZeroScalarSpace m d q f u J counts O) := by
  letI : Module.Finite K (Space m d q f u J counts O) := finite_space hO
  exact Module.Finite.of_injective zeroPrivateScalar zeroPrivateScalar_injective

theorem forms_polynomial_linear_parameters {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (L : V →ₗ[K] Space m d q f u J counts O) (hd : 0 < d)
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j) (hJ : ∀ j∈J,j≤d) :
    IsPolynomialFamily (fun a : Fin (finrank K V) → K =>
      forms hd hO hJ (L ((Module.finBasis K V).equivFun.symm a))) :=
  isPolynomialFamily_linear (((forms hd hO hJ).comp L).comp
    (Module.finBasis K V).equivFun.symm.toLinearMap)

theorem enumerated_forms_polynomial_linear_parameters {V : Type*} {h : ℕ}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    {O : ℕ → Submodule K (Poly K h)}
    (L : V →ₗ[K] Space m d q f u J counts O) (hd : 0 < d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) :
    IsPolynomialFamily (fun a : Fin (finrank K V) → K =>
      PreparedTarget.enumerateForms (forms hd hO hJ
        (L ((Module.finBasis K V).equivFun.symm a)))) :=
  (forms_polynomial_linear_parameters L hd hO hJ).linear_comp PreparedTarget.enumerateForms

end Froberg.FullPreparedParameters
