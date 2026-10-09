module

public import Froberg.TriangularCovectors
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! Finite triangular elimination, with the bottom target filled separately.
The sources and target blocks may all have different dimensions. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K] {n : ℕ}
variable {V S : Fin (n+1) → Type*}
  [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)]
  [∀ i,AddCommGroup (S i)] [∀ i,Module K (S i)]

/-- The sum of the actual relation maps from every target row. -/
def triangularRowSum (C : (i : Fin (n+1)) → S i →ₗ[K] ((j : Fin (n+1)) → V j)) :
    ((i : Fin (n+1)) → S i) →ₗ[K] ((j : Fin (n+1)) → V j) :=
  ∑ i,(C i).comp (LinearMap.proj i)

@[simp] theorem triangularRowSum_single
    (C : (i : Fin (n+1)) → S i →ₗ[K] ((j : Fin (n+1)) → V j))
    (i : Fin (n+1)) (s : S i) : triangularRowSum C (Pi.single i s)=C i s := by
  classical
  simp only [triangularRowSum,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji,map_zero]
  · simp

/-- Once every positive diagonal row is onto, adjoining the bottom block
makes the complete triangular relation map onto. -/
theorem triangular_surjective_with_bottom
    (C : (i : Fin (n+1)) → S i →ₗ[K] ((j : Fin (n+1)) → V j))
    (hupper : ∀ i j,i<j → ∀ s,C i s j=0)
    (hsurj : ∀ i,i≠0 → Function.Surjective (fun s => C i s i)) :
    Function.Surjective ((LinearMap.single K V 0).coprod (triangularRowSum C)) := by
  classical
  let A := (LinearMap.single K V 0).coprod (triangularRowSum C)
  by_contra hbad
  have htop : A.range<⊤ := lt_top_iff_ne_top.mpr (fun h => hbad (LinearMap.range_eq_top.mp h))
  obtain ⟨ell,hne,hann⟩ := A.range.exists_le_ker_of_lt_top htop
  apply hne
  apply triangular_covector_zero C hupper hsurj
  · intro i _ s
    apply hann
    refine ⟨(0,Pi.single i s),?_⟩
    simp [A]
  · intro v
    apply hann
    refine ⟨(v,0),?_⟩
    simp [A]

/-- The positive target projection is onto even when nothing is assumed
about the scalar row. This is surjectivity modulo the bottom target. -/
theorem triangular_surjective_mod_bottom
    (C : (i : Fin (n+1)) → S i →ₗ[K] ((j : Fin (n+1)) → V j))
    (hupper : ∀ i j,i<j → ∀ s,C i s j=0)
    (hsurj : ∀ i,i≠0 → Function.Surjective (fun s => C i s i)) :
    Function.Surjective (fun s : (i : Fin (n+1)) → S i =>
      fun j : Fin n => triangularRowSum C s j.succ) := by
  intro v
  let w : (j : Fin (n+1)) → V j := Fin.cases 0 v
  obtain ⟨⟨z,s⟩,hs⟩ := triangular_surjective_with_bottom C hupper hsurj w
  refine ⟨s,?_⟩
  funext j
  have he := congrFun hs j.succ
  simpa only [LinearMap.coprod_apply,Pi.add_apply,LinearMap.single_apply,
    Pi.single_eq_of_ne (Fin.succ_ne_zero j),zero_add,w,Fin.cases_succ] using he

end Froberg
