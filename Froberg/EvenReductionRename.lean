module

public import Froberg.PrivateReductionRename
public import Froberg.PreparedActualReduction

@[expose] public section

/-! Output reindexing preserves the ordinary positive-row reduction and
its nonempty principal open, including kernel-constrained output spaces. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial Module
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*} [Fintype σ] [Fintype τ] {n : ℕ}

theorem homogeneous_kernel_rename_eq {X : Type*} [AddCommGroup X] [Module K X]
    (e : σ ≃ τ) (T : MvPolynomial τ K →ₗ[K] X) (j : ℕ) :
    (homogeneousSubmodule σ K j ⊓ (T.comp (rename e).toLinearMap).ker).map
      (rename e).toLinearMap=homogeneousSubmodule τ K j ⊓ T.ker := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨hq.1.rename_isHomogeneous,hq.2⟩
  · intro hp
    have he : rename e (rename e.symm p)=p := (renameEquiv K e).right_inv p
    refine ⟨rename e.symm p,⟨hp.1.rename_isHomogeneous,?_⟩,he⟩
    change T (rename e (rename e.symm p))=0
    rw [he]
    exact hp.2

theorem homogeneous_kernel_rename_finrank {X : Type*} [AddCommGroup X] [Module K X]
    (e : σ ≃ τ) (T : MvPolynomial τ K →ₗ[K] X) (j : ℕ) :
    finrank K ↥(homogeneousSubmodule σ K j ⊓ (T.comp (rename e).toLinearMap).ker)=
      finrank K ↥(homogeneousSubmodule τ K j ⊓ T.ker) := by
  have h := (renameEquiv K e).toLinearEquiv.finrank_map_eq
    (homogeneousSubmodule σ K j ⊓ (T.comp (rename e).toLinearMap).ker)
  change finrank K ((homogeneousSubmodule σ K j ⊓
    (T.comp (rename e).toLinearMap).ker).map (rename e).toLinearMap)=_ at h
  rw [homogeneous_kernel_rename_eq] at h
  exact h.symm

namespace PreparedParameters
variable {d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem even_positive_reduction_output_rename
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (e : σ ≃ τ)
    (p : Space n d q J counts O) (hp : EvenPositiveReduction p) :
    EvenPositiveReduction (outputRename e p) := by
  classical
  let E := e.sumCongr (Equiv.refl (Fin n))
  let F := renameEquiv K E
  have hF (a : MvPolynomial (σ ⊕ Fin n) K) : F a=rename (Sum.map e id) a := rfl
  let wσ := Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)
  let wτ := Sum.elim (fun _ : τ => 1) (fun _ : Fin n => 0)
  intro c hc hce hpositive
  let c₀ := fun i => F.symm (c i)
  let S' := ∑ i,generator (outputRename e p) i*c i
  have hSh : S'.IsHomogeneous (2*d) := by
    apply (homogeneousSubmodule (τ ⊕ Fin n) K (2*d)).sum_mem
    intro i _
    have hi : (generator (outputRename e p) i).IsHomogeneous d := by
      rw [outputRename_generator]
      exact (generator_homogeneous hO hJ p i).rename_isHomogeneous
    change (generator (outputRename e p) i*c i).IsHomogeneous (2*d)
    simpa only [two_mul] using hi.mul (hc i)
  have hSw : S'.IsWeightedHomogeneous wτ 0 := by
    apply (positiveWeightProjection_eq_zero_iff wτ (by intro x; cases x <;> simp [wτ]) S' hSh).mp
    funext r
    exact hpositive r.val r.property.1 r.property.2
  have hS : (∑ i,generator p i*c₀ i)=F.symm S' := by
    apply F.injective
    simp only [map_sum,map_mul,AlgEquiv.apply_symm_apply,c₀,S']
    apply Finset.sum_congr rfl
    intro i _
    rw [outputRename_generator]
    rfl
  have hpositive₀ : ∀ r,0<r → r≤2*d → weightedHomogeneousComponent wσ r
      (∑ i,generator p i*c₀ i)=0 := by
    have hh : (F.symm S').IsWeightedHomogeneous wσ 0 :=
      output_rename_weighted e.symm 1 0 0 S' hSw
    have hz := positiveWeightProjection_zero wσ d (F.symm S') hh
    intro r hr hr'
    rw [hS]
    exact congrFun hz ⟨r,hr,hr'⟩
  obtain ⟨M,z,hc₀,hz,hzw⟩ := hp c₀ (fun i => (hc i).rename_isHomogeneous)
    (fun i => output_rename_parity e.symm 0 (by omega) (c i) (hce i)) hpositive₀
  refine ⟨M,fun i => F (z i),?_,?_,?_⟩
  · funext i
    have hh := congrArg F (congrFun hc₀ i)
    simp only [c₀,AlgEquiv.apply_symm_apply,matrixBoundary,matrixCombination,
      Pi.sub_apply,map_sub,map_sum,map_smul] at hh
    simpa only [matrixBoundary,matrixCombination,Pi.sub_apply,outputRename_generator,hF] using hh
  · intro i hi
    change F (z i)=0
    rw [hz i hi]
    exact F.map_zero
  · intro i
    exact ⟨(hzw i).1.rename_isHomogeneous,output_rename_weighted e 1 0 0 (z i) (hzw i).2⟩

theorem even_positive_reduction_open_output_rename
    [Module.Finite K (Space n d q J counts O)]
    (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (e : σ ≃ τ)
    [Module.Finite K (Space n d q J counts (fun j => (O j).map (rename e).toLinearMap))]
    (D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K)
    (hD : ∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0)
    (hgood : ∀ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
      EvenPositiveReduction p) :
    let A := Space n d q J counts (fun j => (O j).map (rename e).toLinearMap)
    ∃ D' : MvPolynomial (Fin (finrank K A)) K,
      (∃ p : A,eval ((Module.finBasis K A).equivFun p) D'≠0) ∧
      ∀ p : A,eval ((Module.finBasis K A).equivFun p) D'≠0 → EvenPositiveReduction p := by
  let F := outputRenameEquiv (n := n) (d := d) (q := q) (J := J) (counts := counts) (O := O) e
  obtain ⟨D',hD',hgood'⟩ := principal_open_linear_pullback F.symm.toLinearMap
    F.symm.surjective D hD (fun p => EvenPositiveReduction p) hgood
  refine ⟨D',hD',?_⟩
  intro p hp
  have H := even_positive_reduction_output_rename hO hJ e (F.symm p) (hgood' p hp)
  change EvenPositiveReduction (F (F.symm p)) at H
  simpa only [LinearEquiv.apply_symm_apply] using H

def EvenReductionOpen (O : ℕ → Submodule K (MvPolynomial σ K))
    [Module.Finite K (Space n d q J counts O)] : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (Space n d q J counts O))) K,
    (∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
      EvenPositiveReduction p

theorem evenReductionOpen_congr_outputs
    {O O' : ℕ → Submodule K (MvPolynomial σ K)}
    [Module.Finite K (Space n d q J counts O)]
    [Module.Finite K (Space n d q J counts O')]
    (hO : O=O') :
    EvenReductionOpen (n := n) (d := d) (q := q) (J := J) (counts := counts) O ↔
      EvenReductionOpen (n := n) (d := d) (q := q) (J := J) (counts := counts) O' := by
  subst O'
  rfl

theorem even_positive_reduction_open_constraint_rename
    {X : Type*} [AddCommGroup X] [Module K X]
    (T : ℕ → MvPolynomial τ K →ₗ[K] X) (e : σ ≃ τ)
    (hJ : ∀ j∈J,j≤d)
    [Module.Finite K (Space n d q J counts
      (fun j => homogeneousSubmodule σ K j ⊓ ((T j).comp (rename e).toLinearMap).ker))]
    [Module.Finite K (Space n d q J counts
      (fun j => homogeneousSubmodule τ K j ⊓ (T j).ker))]
    (D : MvPolynomial (Fin (finrank K (Space n d q J counts
      (fun j => homogeneousSubmodule σ K j ⊓ ((T j).comp (rename e).toLinearMap).ker)))) K)
    (hD : ∃ p : Space n d q J counts
      (fun j => homogeneousSubmodule σ K j ⊓ ((T j).comp (rename e).toLinearMap).ker),
      eval ((Module.finBasis K _).equivFun p) D≠0)
    (hgood : ∀ p : Space n d q J counts
      (fun j => homogeneousSubmodule σ K j ⊓ ((T j).comp (rename e).toLinearMap).ker),
      eval ((Module.finBasis K _).equivFun p) D≠0 → EvenPositiveReduction p) :
    let A := Space n d q J counts (fun j => homogeneousSubmodule τ K j ⊓ (T j).ker)
    ∃ D' : MvPolynomial (Fin (finrank K A)) K,
      (∃ p : A,eval ((Module.finBasis K A).equivFun p) D'≠0) ∧
      ∀ p : A,eval ((Module.finBasis K A).equivFun p) D'≠0 → EvenPositiveReduction p := by
  let O₀ := fun j => homogeneousSubmodule σ K j ⊓ ((T j).comp (rename e).toLinearMap).ker
  have hmap : (fun j => (O₀ j).map (rename e).toLinearMap)=
      (fun j => homogeneousSubmodule τ K j ⊓ (T j).ker) := by
    funext j
    exact homogeneous_kernel_rename_eq e (T j) j
  letI : Module.Finite K (Space n d q J counts (fun j => (O₀ j).map (rename e).toLinearMap)) := by
    rw [hmap]
    infer_instance
  have H := even_positive_reduction_open_output_rename (O := O₀)
    (fun _ _ => inf_le_left) hJ e D hD hgood
  exact (evenReductionOpen_congr_outputs hmap).mp H

end PreparedParameters
end Froberg
