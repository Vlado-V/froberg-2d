module

public import Froberg.AttachedFibers
public import Quartic.QuotientBilinearImage

@[expose] public section

/-! Genuine polynomial multiplication on the attached outer-module quotients. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open MvPolynomial
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] {n s d : ℕ}

/-- Scalar multiplication of a vector of homogeneous forms by a homogeneous form. -/
def vectorMultiply : Forms K n d →ₗ[K] (J → Forms K n s) →ₗ[K] (J → Forms K n (s+d)) where
  toFun f :=
    { toFun := fun p j => ⟨f.val * (p j).val,by
        simpa only [Forms,mem_homogeneousSubmodule,add_comm] using f.property.mul (p j).property⟩
      map_add' := by intro p q; funext j; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro c p; funext j; apply Subtype.ext; exact mul_smul_comm _ _ _ }
  map_add' := by intro f g; apply LinearMap.ext; intro p; funext j; apply Subtype.ext; exact add_mul _ _ _
  map_smul' := by intro c f; apply LinearMap.ext; intro p; funext j; apply Subtype.ext; exact smul_mul_assoc _ _ _

@[simp] theorem vectorMultiply_val (f : Forms K n d) (p : J → Forms K n s) (j : J) :
    (vectorMultiply f p j).val = f.val * (p j).val := rfl

/-- Multiplying an actual presentation relation produces an actual higher-degree relation. -/
theorem vectorMultiply_relation (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (f : Forms K n d)
    (p : J → Forms K n s) (hp : p ∈ relationSpace (d := 0) e v he) :
    vectorMultiply f p ∈ relationSpace (d := d) e v he := by
  obtain ⟨a,rfl⟩ := hp
  let b : I → Forms K n d := fun i => ⟨f.val * (a i).val,by
    simpa only [Forms,mem_homogeneousSubmodule,add_zero] using f.property.mul (a i).property⟩
  refine ⟨b,?_⟩
  funext j
  apply Subtype.ext
  change (∑ i, monomial (e i) (v i j) * (f.val * (a i).val)) =
    f.val * (∑ i, monomial (e i) (v i j) * (a i).val)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Multiplication on the genuine source and target quotients. -/
def quotientMultiply (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) :
    Forms K n d →ₗ[K]
      ((J → Forms K n s) ⧸ relationSpace (d := 0) e v he) →ₗ[K]
      ((J → Forms K n (s+d)) ⧸ relationSpace (d := d) e v he) where
  toFun f := (relationSpace (d := 0) e v he).liftQ
    ((relationSpace (d := d) e v he).mkQ.comp (vectorMultiply f)) (by
      intro p hp
      exact (Submodule.Quotient.mk_eq_zero _).mpr (vectorMultiply_relation e v he f p hp))
  map_add' f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨p,rfl⟩ := (relationSpace (d := 0) e v he).mkQ_surjective x
    change (relationSpace (d := d) e v he).mkQ (vectorMultiply (f+g) p) =
      (relationSpace (d := d) e v he).mkQ (vectorMultiply f p) +
      (relationSpace (d := d) e v he).mkQ (vectorMultiply g p)
    simp
  map_smul' c f := by
    apply LinearMap.ext
    intro x
    obtain ⟨p,rfl⟩ := (relationSpace (d := 0) e v he).mkQ_surjective x
    change (relationSpace (d := d) e v he).mkQ (vectorMultiply (c • f) p) =
      c • (relationSpace (d := d) e v he).mkQ (vectorMultiply f p)
    simp

@[simp] theorem quotientMultiply_mk (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i, (e i).degree = s) (f : Forms K n d) (p : J → Forms K n s) :
    quotientMultiply e v he f ((relationSpace (d := 0) e v he).mkQ p) =
      (relationSpace (d := d) e v he).mkQ (vectorMultiply f p) := rfl

end Froberg.AttachedMultiplication
