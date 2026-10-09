module

public import Froberg.GenericDimensions

@[expose] public section

/-! A nonzero replacement parameter in every prescribed finite intersection
of principal opens through the undeformed family. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K : Type*} [Field K] [Infinite K]

theorem exists_nonzero_replacement_parameter (P : MvPolynomial Unit K)
    (hP : eval (fun _ => 0) P ≠ 0) :
    ∃ e : K,e ≠ 0 ∧ eval (fun _ => e) P ≠ 0 := by
  have hX : ∃ p : Unit → K,eval p (X ()) ≠ 0 := ⟨fun _ => 1,by simp⟩
  obtain ⟨p,hp,hx⟩ := principal_opens_intersect ⟨fun _ => 0,hP⟩ hX
  refine ⟨p (),by simpa using hx,?_⟩
  have he : (fun _ : Unit => p ())=p := by funext i; cases i; rfl
  rwa [he]

theorem exists_nonzero_replacement_intersection {S : Type*} [Fintype S]
    (P : S → MvPolynomial Unit K) (hP : ∀ i,eval (fun _ => 0) (P i) ≠ 0) :
    ∃ e : K,e ≠ 0 ∧ ∀ i,eval (fun _ => e) (P i) ≠ 0 := by
  classical
  obtain ⟨e,he,hgood⟩ := exists_nonzero_replacement_parameter (∏ i,P i)
    (by simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  refine ⟨e,he,?_⟩
  simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hgood

theorem exists_nonzero_replacement_fin (P : MvPolynomial (Fin 1) K)
    (hP : eval 0 P ≠ 0) :
    ∃ e : K,e ≠ 0 ∧ eval (fun _ => e) P ≠ 0 := by
  have hX : ∃ p : Fin 1 → K,eval p (X 0) ≠ 0 := ⟨fun _ => 1,by simp⟩
  obtain ⟨p,hp,hx⟩ := principal_opens_intersect ⟨0,hP⟩ hX
  refine ⟨p 0,by simpa using hx,?_⟩
  have he : (fun _ : Fin 1 => p 0)=p := by
    funext i
    congr 1
    exact Subsingleton.elim _ _
  rwa [he]

theorem exists_nonzero_replacement_fin_intersection {S : Type*} [Fintype S]
    (P : S → MvPolynomial (Fin 1) K) (hP : ∀ i,eval 0 (P i) ≠ 0) :
    ∃ e : K,e ≠ 0 ∧ ∀ i,eval (fun _ => e) (P i) ≠ 0 := by
  classical
  obtain ⟨e,he,hgood⟩ := exists_nonzero_replacement_fin (∏ i,P i)
    (by simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  refine ⟨e,he,?_⟩
  simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hgood

end Froberg
