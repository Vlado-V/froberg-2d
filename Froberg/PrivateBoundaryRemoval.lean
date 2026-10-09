module

public import Froberg.MatrixKoszul
public import Froberg.BoundedWeightedComponents

@[expose] public section

/-! Removing the private-private boundary in the first even output row uses
the full U+P generator, so it preserves the actual cycle. -/
noncomputable section
namespace Froberg
open Finset MvPolynomial
variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B] {r : ℕ}

theorem matrixBoundary_map (L : A →ₗ[K] B) (q : Fin r → A) (C : Fin r → Fin r → K) :
    (fun i => L (matrixBoundary q C i))=matrixBoundary (fun i => L (q i)) C := by
  funext i
  simp only [matrixBoundary,matrixCombination,Pi.sub_apply,map_sub,map_sum,map_smul]

/-- Every literal constant Koszul vector is represented by one coefficient
matrix, including in characteristic two. -/
theorem exists_matrixBoundary_of_mem_koszul (q : Fin r → A) (u : Fin r → A)
    (hu : u∈Submodule.span K (Set.range (koszulVector q))) :
    ∃ C : Fin r → Fin r → K,matrixBoundary q C=u := by
  classical
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,rfl⟩ := hx
    refine ⟨Pi.single p.val.1 (Pi.single p.val.2 1),?_⟩
    funext k
    have hpne : p.val.1≠p.val.2 := ne_of_lt p.property
    by_cases h1 : k=p.val.1 <;> by_cases h2 : k=p.val.2 <;>
      simp [matrixBoundary,matrixCombination,koszulVector,Pi.single_apply,ite_apply,h1,h2,hpne,eq_comm]
  | zero => exact ⟨0,by ext i; simp [matrixBoundary,matrixCombination]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨C,hC⟩ := ihx
    obtain ⟨D,hD⟩ := ihy
    refine ⟨C+D,?_⟩
    rw [←hC,←hD]
    ext i
    simp only [matrixBoundary,matrixCombination,Pi.sub_apply,Pi.add_apply,add_smul,sum_add_distrib]
    abel
  | smul c x hx ih =>
    obtain ⟨C,hC⟩ := ih
    refine ⟨c • C,?_⟩
    rw [←hC]
    ext i
    simp only [matrixBoundary,matrixCombination,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      mul_smul,←smul_sum,smul_sub]

/-- The low component of a full private boundary is precisely its P-boundary. -/
theorem private_matrixBoundary_component {σ : Type*}
    (w : σ → ℕ) (U P : Fin r → MvPolynomial σ K) {d : ℕ} (hd : d≠1)
    (hU : ∀ i,(U i).IsWeightedHomogeneous w d)
    (hP : ∀ i,(P i).IsWeightedHomogeneous w 1)
    (C : Fin r → Fin r → K) :
    (fun i => weightedHomogeneousComponent w 1 (matrixBoundary (fun i => U i+P i) C i))=
      matrixBoundary P C := by
  rw [matrixBoundary_map]
  congr 1
  funext i
  simp only [map_add,weightedHomogeneousComponent_of_mem (hU i),
    weightedHomogeneousComponent_of_mem (hP i),ite_true,if_neg (Ne.symm hd),zero_add]

/-- Subtracting the full U+P boundary kills the first private coefficient
component and changes no polynomial relation. -/
theorem remove_private_first_component {σ : Type*}
    (w : σ → ℕ) (U P u : Fin r → MvPolynomial σ K) {d : ℕ} (hd : d≠1)
    (hU : ∀ i,(U i).IsWeightedHomogeneous w d)
    (hP : ∀ i,(P i).IsWeightedHomogeneous w 1)
    (hu : (fun i => weightedHomogeneousComponent w 1 (u i))∈
      Submodule.span K (Set.range (koszulVector P))) :
    ∃ C : Fin r → Fin r → K,
      (∀ i,weightedHomogeneousComponent w 1 ((u-matrixBoundary (fun i => U i+P i) C) i)=0) ∧
      ∑ i,(U i+P i)*(u-matrixBoundary (fun i => U i+P i) C) i=∑ i,(U i+P i)*u i := by
  obtain ⟨C,hC⟩ := exists_matrixBoundary_of_mem_koszul P _ hu
  refine ⟨C,?_,?_⟩
  · intro i
    have hcomp := congrFun (private_matrixBoundary_component w U P hd hU hP C) i
    simp only [Pi.sub_apply,map_sub,hcomp,congrFun hC i,sub_self]
  · simp only [Pi.sub_apply,mul_sub,sum_sub_distrib,matrixBoundary_cycle,sub_zero]

end Froberg
