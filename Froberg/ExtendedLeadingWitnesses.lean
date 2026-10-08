import Froberg.ExtendedEvenRowWitnesses
import Froberg.PreparedLeadingWitness
import Froberg.PrivateBiformFamily

/-! Literal independent high components survive extension of the scalar variables. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d q : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem quadratic_only_extended_leading
    (hd : 3≤d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,2≤j) (hJd : ∀ j∈J,j≤d) (h2 : 2∈J)
    (hz : ∀ j∈J,j≠2 → counts j=0)
    (hquad : ∃ b,QuadraticRowCapacity a d q b J counts O)
    (ell : Fin 2 → Forms K a 1) (hell : LinearIndependent K ell) :
    ∀ R : J,∃ p : Space (a+z) d q J counts O,LinearIndependent K (p.2 R) := by
  classical
  intro R
  by_cases hR : R.val=2
  · have hReq : R=(⟨2,h2⟩ : J) := Subtype.ext hR
    subst R
    obtain ⟨b,hb⟩ := hquad
    obtain ⟨p,hp,_⟩ := exists_quadratic_extended_row_parameter (z := z)
      hd hO hJ hJd h2 hb ell hell
    exact ⟨p,(intrinsicLayer_independent_iff hO p ⟨2,h2⟩).mp hp⟩
  · have hzero := hz R.val R.property hR
    letI : IsEmpty (Fin (counts R.val)) := ⟨fun i => by have := i.isLt; omega⟩
    exact ⟨0,linearIndependent_empty_type⟩

variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem all_even_extended_leading {w v z d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    (hd : 3≤d) (hv : 0<v)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hJ : ∀ j∈J,2≤j) (hJd : ∀ j∈J,j≤d) (h2 : 2∈J)
    (hquad : ∃ b,QuadraticRowCapacity (v+v) d q b J counts (constrainedOutputs T))
    (hhigher : ∀ R : J,R.val≠2 → ∃ b,HigherRowCapacity w v d q b J counts T R) :
    ∀ R : J,∃ p : Space (v+v+z) d q J counts (constrainedOutputs T),
      LinearIndependent K (p.2 R) := by
  classical
  obtain ⟨ell,hell⟩ := exists_two_core_linear_forms (K := K) (by omega : 2≤v+v)
  apply leading_witnesses_of_intrinsic (fun _ _ => inf_le_left)
  intro R
  by_cases hR : R.val=2
  · have hReq : R=(⟨2,h2⟩ : J) := Subtype.ext hR
    subst R
    obtain ⟨b,hb⟩ := hquad
    obtain ⟨p,hp,_⟩ := exists_quadratic_extended_row_parameter (z := z)
      hd (fun _ _ => inf_le_left) hJ hJd h2 hb ell hell
    exact ⟨p,hp⟩
  · obtain ⟨b,hb⟩ := hhigher R hR
    obtain ⟨p,hp,_⟩ := exists_higher_extended_row_parameter (z := z) R hb ell hell
    exact ⟨p,hp⟩

end Froberg.PreparedParameters
