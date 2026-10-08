import Froberg.OddSplitElimination

/-! Literal two-family relation statements are invariant under finite
reindexing of either family. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K A I J I' J' : Type*} [Field K] [CommRing A] [Algebra K A]
  [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

theorem constant_pair_kernel_reindex (e : I ≃ I') (f : J ≃ J')
    (S : I → A) (O : J → A) (U V : Submodule K A)
    (h : ∀ (x : I' → A) (y : J' → A),
      (∀ i,x i∈U) → (∀ j,y j∈V) →
      (∑ i,S (e.symm i)*x i)+(∑ j,O (f.symm j)*y j)=0 →
      ∃ C : I' → J' → K,
        (∀ i,x i=∑ j,C i j • O (f.symm j)) ∧
        (∀ j,y j = -∑ i,C i j • S (e.symm i)))
    (x : I → A) (y : J → A) (hx : ∀ i,x i∈U) (hy : ∀ j,y j∈V)
    (hr : (∑ i,S i*x i)+(∑ j,O j*y j)=0) :
    ∃ C : I → J → K,
      (∀ i,x i=∑ j,C i j • O j) ∧ (∀ j,y j = -∑ i,C i j • S i) := by
  have hr' : (∑ i,S (e.symm i)*x (e.symm i))+
      (∑ j,O (f.symm j)*y (f.symm j))=0 := by
    rw [e.symm.sum_comp (fun i => S i*x i),f.symm.sum_comp (fun j => O j*y j)]
    exact hr
  obtain ⟨C,hC,hC'⟩ := h (x ∘ e.symm) (y ∘ f.symm)
    (fun i => hx _) (fun j => hy _) hr'
  refine ⟨fun i j => C (e i) (f j),?_,?_⟩
  · intro i
    have hh := hC (e i)
    simp only [Function.comp_apply,Equiv.symm_apply_apply] at hh
    rw [hh]
    simpa only [Equiv.symm_apply_apply] using
      (f.sum_comp (fun j => C (e i) j • O (f.symm j))).symm
  · intro j
    have hh := hC' (f j)
    simp only [Function.comp_apply,Equiv.symm_apply_apply] at hh
    rw [hh]
    congr 1
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun i => C i (f j) • S (e.symm i))).symm

theorem injective_pair_kernel_reindex (e : I ≃ I') (f : J ≃ J')
    (S : I → A) (O : J → A) (U V : Submodule K A)
    (h : ∀ (x : I' → A) (y : J' → A),
      (∀ i,x i∈U) → (∀ j,y j∈V) →
      (∑ i,S (e.symm i)*x i)+(∑ j,O (f.symm j)*y j)=0 → x=0 ∧ y=0)
    (x : I → A) (y : J → A) (hx : ∀ i,x i∈U) (hy : ∀ j,y j∈V)
    (hr : (∑ i,S i*x i)+(∑ j,O j*y j)=0) : x=0 ∧ y=0 := by
  have hr' : (∑ i,S (e.symm i)*x (e.symm i))+
      (∑ j,O (f.symm j)*y (f.symm j))=0 := by
    rw [e.symm.sum_comp (fun i => S i*x i),f.symm.sum_comp (fun j => O j*y j)]
    exact hr
  obtain ⟨hx0,hy0⟩ := h (x ∘ e.symm) (y ∘ f.symm)
    (fun i => hx _) (fun j => hy _) hr'
  constructor
  · funext i
    simpa using congrFun hx0 (e i)
  · funext j
    simpa using congrFun hy0 (f j)

end Froberg
