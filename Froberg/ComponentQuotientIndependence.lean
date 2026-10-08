import Froberg.WeightedFamilyIndependence

/-! Component projections detect independence modulo a scalar subspace,
even when each generator contains additional higher-weight terms. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem quotient_independent_of_projection {I : Type*}
    (A : Submodule K V) (g : I → V) (P : V →ₗ[K] W)
    (hA : A≤P.ker) (hg : LinearIndependent K (fun i => P (g i))) :
    LinearIndependent K (fun i => A.mkQ (g i)) := by
  apply LinearIndependent.of_comp (A.liftQ P hA)
  simpa only [Function.comp_def,Submodule.mkQ_apply,Submodule.liftQ_apply] using hg


theorem quotient_split_independent {I L : Type*} [Fintype I] [Fintype L]
    (A : Submodule K V) (g : I → V) (v : L → V) (P : V →ₗ[K] W)
    (hA : A≤P.ker) (hg : LinearIndependent K (fun i => A.mkQ (g i)))
    (hv : LinearIndependent K (fun i => P (v i))) (hzero : ∀ i,P (g i)=0) :
    LinearIndependent K (fun i : I ⊕ L => A.mkQ (Sum.elim g v i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hm : (∑ k,c k • Sum.elim g v k)∈A := by
    apply (Submodule.Quotient.mk_eq_zero A).mp
    change A.mkQ (∑ k,c k • Sum.elim g v k)=0
    simpa only [map_sum,map_smul] using hc
  have hp := hA hm
  change P (∑ k,c k • Sum.elim g v k)=0 at hp
  simp only [map_sum,map_smul,map_add,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    hzero,smul_zero,Finset.sum_const_zero,zero_add] at hp
  have hz : ∀ j,c (Sum.inr j)=0 := Fintype.linearIndependent_iff.mp hv _ hp
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,hz,zero_smul,
    Finset.sum_const_zero,add_zero] at hc
  cases i with
  | inl i => exact Fintype.linearIndependent_iff.mp hg _ hc i
  | inr i => exact hz i

variable {σ : Type*} {w : σ → ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}

theorem component_quotient_family_independent
    (A : Submodule K (MvPolynomial σ K))
    (g : (j : J) → Fin (counts j.val) → MvPolynomial σ K)
    (v : (Σ j : J,Fin (counts j.val)) → MvPolynomial σ K)
    (hA : ∀ j : J,0<counts j.val → ∀ a∈A,weightedHomogeneousComponent w j.val a=0)
    (hcomp : ∀ (j k : J) (i : Fin (counts k.val)),0<counts j.val →
      weightedHomogeneousComponent w j.val (v ⟨k,i⟩)=if k=j then g k i else 0)
    (hg : ∀ j,LinearIndependent K (g j)) :
    LinearIndependent K (fun i => A.mkQ (v i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hmem : (∑ k,c k • v k)∈A := by
    apply (Submodule.Quotient.mk_eq_zero A).mp
    change A.mkQ (∑ k,c k • v k)=0
    simpa only [map_sum,map_smul] using hc
  have hip : 0<counts i.1.val := Nat.zero_lt_of_lt i.2.isLt
  have hrel := hA i.1 hip _ hmem
  simp only [map_sum,map_smul,Fintype.sum_sigma,fun k l => hcomp i.1 k l hip] at hrel
  have hi : (∑ k,c ⟨i.1,k⟩ • g i.1 k)=0 := by
    simpa [smul_ite] using hrel
  exact Fintype.linearIndependent_iff.mp (hg i.1) _ hi i.2

end Froberg
