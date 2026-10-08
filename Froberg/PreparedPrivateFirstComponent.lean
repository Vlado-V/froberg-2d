import Froberg.PreparedPrivateCoefficientProperty
import Froberg.PreparedPrivateKernels
import Froberg.PreparedEvenReduction

/-! The exact augmented first row detects the literal private-private
boundary in the first weighted component of an actual coefficient tuple. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d q b : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_first_coefficient_boundary
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (hpos : ∀ j∈J,0<j) (h2 : 2∈J)
    (p : Space n d q J counts O) (P : Fin b → FullBiform K σ n 1 (d-1))
    (hrow : (privateAugmentedRow hO ⟨2,h2⟩ p (fun i => (P i).val)).ker=
      ((rowConstants hO ⟨2,h2⟩ p).prodMap (intrinsicPrivateBoundary P)).range)
    (x f : Label q J counts → MvPolynomial (σ ⊕ Fin n) K)
    (u : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hx : ∀ i,x i∈coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d 2)
    (hf : ∀ i,f i∈coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d 0)
    (hu : ∀ i,u i∈coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d 1)
    (hrel : (∑ i,scalar p i*x i)+(∑ i,if degree i=2 then high p i*f i else 0)+
      (∑ i,(P i).val*u i)=0) :
    u∈Submodule.span K (Set.range (koszulVector (fun i => (P i).val))) := by
  classical
  apply private_coefficient_row_property hO hJ hpos ⟨2,h2⟩ p (fun i => (P i).val)
    (fun u => u∈Submodule.span K (Set.range (koszulVector (fun i => (P i).val))))
    (by
      intro x u hrel
      obtain ⟨C,hC⟩ := addRow_private_mem_of_exact _ _ _ _ hrow x u hrel
      have hv : (fun i => (u i).val)=matrixBoundary (fun i => (P i).val) C := by
        funext i
        rw [←hC]
        exact intrinsicPrivateBoundary_val P C i
      rw [hv]
      exact matrixBoundary_mem_koszul _ C)
    x f 0 u hx hf hu (by intros; rfl)
  simpa only [Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero] using hrel

theorem private_first_component_boundary
    (hd : 3≤d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (hmin : ∀ j∈J,2≤j) (h2 : 2∈J)
    (p : Space n d q J counts O) (P : Fin b → FullBiform K σ n 1 (d-1))
    (hrow : (privateAugmentedRow hO ⟨2,h2⟩ p (fun i => (P i).val)).ker=
      ((rowConstants hO ⟨2,h2⟩ p).prodMap (intrinsicPrivateBoundary P)).range)
    (U : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hU : ∀ i,(U i).IsWeightedHomogeneous (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
    (c : Label q J counts → MvPolynomial (σ ⊕ Fin n) K)
    (v : Fin b → MvPolynomial (σ ⊕ Fin n) K)
    (hc : ∀ i,(c i).IsHomogeneous d) (hv : ∀ i,(v i).IsHomogeneous d)
    (hpositive : weightedHomogeneousComponent (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 2
      ((∑ i,generator p i*c i)+(∑ k,((P k).val+U k)*v k))=0) :
    (fun k => weightedHomogeneousComponent (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 1 (v k))∈
      Submodule.span K (Set.range (koszulVector (fun k => (P k).val))) := by
  classical
  let w := Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)
  have hscalar (i : Label q J counts) : (scalar p i).IsWeightedHomogeneous w 0 :=
    rename_weightedHomogeneous (⟨Sum.inr,Sum.inr_injective⟩ : Fin n ↪ σ ⊕ Fin n)
      (fun _ => 0) w (fun _ => rfl) (weightedHomogeneous_zero_weight (p.1 i).val)
  have hP (k) : (P k).val.IsWeightedHomogeneous w 1 :=
    biformImage_output_weight _ _ le_rfl (P k).property
  have hprivate : weightedHomogeneousComponent w 2 (∑ k,((P k).val+U k)*v k)=
      ∑ k,(P k).val*weightedHomogeneousComponent w 1 (v k) := by
    simp only [map_sum,add_mul,map_add,weightedComponent_homogeneous_left w (hP _),
      weightedComponent_homogeneous_left w (hU _),if_pos (by decide : 1≤2),
      if_neg (by omega : ¬d≤2),add_zero]
  have hnew (i : Label q J counts) :
      (if degree i≤2 then high p i*weightedHomogeneousComponent w (2-degree i) (c i) else 0)=
      if degree i=2 then high p i*weightedHomogeneousComponent w 0 (c i) else 0 := by
    cases i with
    | inl i => simp only [degree,Sum.elim_inl,high_scalar_label,zero_mul,ite_self]
    | inr a =>
      have hm := hmin _ a.1.property
      by_cases ha : a.1.val=2
      · simp only [degree,Sum.elim_inr,ha,le_refl,if_true,Nat.sub_self]
      · have hgt : ¬a.1.val≤2 := by omega
        simp only [degree,Sum.elim_inr,if_neg ha,if_neg hgt]
  have hh := hpositive
  change weightedHomogeneousComponent w 2 _=0 at hh
  rw [map_add,hprivate] at hh
  rw [show (∑ i,generator p i*c i)=∑ i,(scalar p i+high p i)*c i from rfl,
    mixed_generator_component_row w (scalar p) (high p) c degree hscalar (high_weight hO p) 2] at hh
  simp only [hnew] at hh
  apply private_first_coefficient_boundary hO hJ (fun j hj => by have := hmin j hj; omega)
    h2 p P hrow (fun i => weightedHomogeneousComponent w 2 (c i))
      (fun i => weightedHomogeneousComponent w 0 (c i))
      (fun i => weightedHomogeneousComponent w 1 (v i))
      (fun i => ⟨weightedComponent_preserves_homogeneous w (hc i) 2,
        weightedHomogeneousComponent_isWeightedHomogeneous 2 (c i)⟩)
      (fun i => ⟨weightedComponent_preserves_homogeneous w (hc i) 0,
        weightedHomogeneousComponent_isWeightedHomogeneous 0 (c i)⟩)
      (fun i => ⟨weightedComponent_preserves_homogeneous w (hv i) 1,
        weightedHomogeneousComponent_isWeightedHomogeneous 1 (v i)⟩)
  exact hh

end Froberg.PreparedParameters
