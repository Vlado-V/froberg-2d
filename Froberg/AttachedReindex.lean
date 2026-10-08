import Froberg.AttachedGenerators

/-! Reindexing an attached presentation changes none of its polynomial relations. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module
variable {K I I' J : Type*} [Field K] [Fintype I] [Fintype I'] [Fintype J]
  {n s d : ℕ}

lemma multiplication_reindex (r : I' ≃ I) (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (a : I' → Forms K n d) :
    multiplication (e ∘ r) (v ∘ r) a=multiplication e v (a ∘ r.symm) := by
  funext j
  have heq := r.sum_comp (fun i => MvPolynomial.monomial (e i) (v i j)*(a (r.symm i)).val)
  simpa only [multiplication_apply,Function.comp_apply,Equiv.symm_apply_apply] using heq

lemma homogeneousMultiplication_reindex (r : I' ≃ I) (e : I → Fin n →₀ ℕ)
    (v : I → J → K) (he : ∀ i,(e i).degree=s) (a : I' → Forms K n d) :
    homogeneousMultiplication (e ∘ r) (v ∘ r) (fun i => he (r i)) a=
      homogeneousMultiplication e v he (a ∘ r.symm) := by
  funext j
  apply Subtype.ext
  exact congrFun (multiplication_reindex r e v a) j

lemma multiplication_injective_reindex (r : I' ≃ I) (e : I → Fin n →₀ ℕ)
    (v : I → J → K) (hi : Function.Injective (multiplication (d := d) e v)) :
    Function.Injective (multiplication (d := d) (e ∘ r) (v ∘ r)) := by
  intro a b hab
  rw [multiplication_reindex,multiplication_reindex] at hab
  have hh := hi hab
  funext i
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun hh (r i)

lemma relationSpace_reindex (r : I' ≃ I) (e : I → Fin n →₀ ℕ)
    (v : I → J → K) (he : ∀ i,(e i).degree=s) :
    relationSpace (d := d) (e ∘ r) (v ∘ r) (fun i => he (r i))=relationSpace (d := d) e v he := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a ∘ r.symm,(homogeneousMultiplication_reindex r e v he a).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a ∘ r,?_⟩
    rw [homogeneousMultiplication_reindex]
    congr 1
    funext i
    simp

end Froberg.AttachedMultiplication
