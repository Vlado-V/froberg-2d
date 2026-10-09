module

public import Froberg.PreparedPrivateWitnessOpen
public import Froberg.PreparedOutputEquiv
public import Froberg.RestorationRename
public import Froberg.ParameterPullbackOpen

@[expose] public section

/-! Reindexing the output variables transports the complete private
reduction, including the restored pure tuple and the literal boundaries. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*} [Fintype σ] [Fintype τ] {n : ℕ}

theorem output_rename_weighted {M : Type*} [AddCommMonoid M]
    (e : σ ≃ τ) (x y r : M) (f : MvPolynomial (σ ⊕ Fin n) K)
    (hf : f.IsWeightedHomogeneous (Sum.elim (fun _ : σ => x) (fun _ : Fin n => y)) r) :
    (rename (Sum.map e id) f).IsWeightedHomogeneous
      (Sum.elim (fun _ : τ => x) (fun _ : Fin n => y)) r := by
  apply weighted_homogeneous_rename (e.sumCongr (Equiv.refl (Fin n))).toEmbedding
  convert hf using 1
  funext a
  cases a <;> rfl

theorem output_rename_parity (e : σ ≃ τ) (p : ℕ) (hp : p<2)
    (f : MvPolynomial (σ ⊕ Fin n) K)
    (hf : ∀ a,f.coeff a≠0 → Finsupp.weight
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) a%2=p) :
    ∀ a,(rename (Sum.map e id) f).coeff a≠0 → Finsupp.weight
      (Sum.elim (fun _ : τ => 1) (fun _ : Fin n => 0)) a%2=p := by
  apply (parity_homogeneous_iff _ _ p hp).mp
  have hcastτ : (fun i : τ ⊕ Fin n =>
      ((Sum.elim (fun _ : τ => (1 : ℕ)) (fun _ : Fin n => 0) i : ℕ) : ZMod 2))=
      Sum.elim (fun _ : τ => (1 : ZMod 2)) (fun _ : Fin n => 0) := by
    funext i; cases i <;> simp
  rw [hcastτ]
  apply output_rename_weighted e (1 : ZMod 2) 0 (p : ZMod 2) f
  convert (parity_homogeneous_iff _ f p hp).mpr hf using 1
  funext a
  cases a <;> rfl

namespace PreparedParameters
variable {d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem private_positive_reduction_output_rename
    (hd : 0<d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (e : σ ≃ τ)
    (p : Space n d q J counts O) (P : Fin b → FullBiform K σ n 1 (d-1))
    (P' : Fin b → FullBiform K τ n 1 (d-1))
    (hP' : ∀ i,(P' i).val=rename (Sum.map e id) (P i).val)
    (hp : PrivatePositiveReduction p P) :
    PrivatePositiveReduction (outputRename e p) P' := by
  classical
  let E := e.sumCongr (Equiv.refl (Fin n))
  let F := renameEquiv K E
  have hF (a : MvPolynomial (σ ⊕ Fin n) K) : F a=rename (Sum.map e id) a := rfl
  let wσ := Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)
  let wτ := Sum.elim (fun _ : τ => 1) (fun _ : Fin n => 0)
  intro U hU c v hc hv hce hvodd hpositive
  let U₀ := fun i => F.symm (U i)
  let c₀ := fun i => F.symm (c i)
  let v₀ := fun i => F.symm (v i)
  have hU₀ : ∀ i,(U₀ i).IsHomogeneous d ∧ (U₀ i).IsWeightedHomogeneous wσ d := by
    intro i
    exact ⟨(hU i).1.rename_isHomogeneous,output_rename_weighted e.symm 1 0 d (U i) (hU i).2⟩
  let S' := (∑ i,generator (outputRename e p) i*c i)+(∑ i,((P' i).val+U i)*v i)
  have hSh : S'.IsHomogeneous (2*d) := by
    apply IsHomogeneous.add
    · apply (homogeneousSubmodule (τ ⊕ Fin n) K (2*d)).sum_mem
      intro i _
      have hi : (generator (outputRename e p) i).IsHomogeneous d := by
        rw [outputRename_generator]
        exact (generator_homogeneous hO hJ p i).rename_isHomogeneous
      change (generator (outputRename e p) i*c i).IsHomogeneous (2*d)
      simpa only [two_mul] using hi.mul (hc i)
    · apply (homogeneousSubmodule (τ ⊕ Fin n) K (2*d)).sum_mem
      intro i _
      have hPi : (P' i).val.IsHomogeneous d := by
        have hh := biformImage_homogeneous _ _ le_rfl le_rfl (P' i).property
        change (P' i).val.IsHomogeneous (1+(d-1)) at hh
        simpa only [show 1+(d-1)=d by omega] using hh
      change (((P' i).val+U i)*v i).IsHomogeneous (2*d)
      simpa only [two_mul] using (hPi.add (hU i).1).mul (hv i)
  have hSw : S'.IsWeightedHomogeneous wτ 0 := by
    apply (positiveWeightProjection_eq_zero_iff wτ (by intro x; cases x <;> simp [wτ]) S' hSh).mp
    funext r
    exact hpositive r.val r.property.1 r.property.2
  have hS : (∑ i,generator p i*c₀ i)+(∑ i,((P i).val+U₀ i)*v₀ i)=F.symm S' := by
    apply F.injective
    simp only [map_add,map_sum,map_mul,AlgEquiv.apply_symm_apply,U₀,c₀,v₀,S']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [outputRename_generator]
      rfl
    · apply Finset.sum_congr rfl
      intro i _
      rw [hP']
      rfl
  have hpositive₀ : ∀ r,0<r → r≤2*d → weightedHomogeneousComponent wσ r
      ((∑ i,generator p i*c₀ i)+(∑ i,((P i).val+U₀ i)*v₀ i))=0 := by
    have hh : (F.symm S').IsWeightedHomogeneous wσ 0 := output_rename_weighted e.symm 1 0 0 S' hSw
    have hz := positiveWeightProjection_zero wσ d (F.symm S') hh
    intro r hr hr'
    rw [hS]
    exact congrFun hz ⟨r,hr,hr'⟩
  obtain ⟨C,M,z,hv₀,hc₀,hz,hzw⟩ := hp U₀ hU₀ c₀ v₀
    (fun i => (hc i).rename_isHomogeneous) (fun i => (hv i).rename_isHomogeneous)
    (fun i => output_rename_parity e.symm 0 (by omega) (c i) (hce i))
    (fun i => output_rename_parity e.symm 1 (by omega) (v i) (hvodd i)) hpositive₀
  refine ⟨C,M,fun i => F (z i),?_,?_,?_,?_⟩
  · funext i
    have hh := congrArg F (congrFun hv₀ i)
    simp only [v₀,U₀,AlgEquiv.apply_symm_apply,matrixBoundary,matrixCombination,
      Pi.sub_apply,map_sub,map_sum,map_smul,map_add] at hh
    simpa only [matrixBoundary,matrixCombination,Pi.sub_apply,hP',hF] using hh
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

theorem private_positive_reduction_open_output_rename
    [Module.Finite K (Space n d q J counts O)]
    (hd : 0<d) (hO : ∀ j∈J,O j≤homogeneousSubmodule σ K j)
    (hJ : ∀ j∈J,j≤d) (e : σ ≃ τ)
    [Module.Finite K (Space n d q J counts (fun j => (O j).map (rename e).toLinearMap))]
    (P : Fin b → FullBiform K σ n 1 (d-1))
    (P' : Fin b → FullBiform K τ n 1 (d-1))
    (hP' : ∀ i,(P' i).val=rename (Sum.map e id) (P i).val)
    (D : MvPolynomial (Fin (Module.finrank K (Space n d q J counts O))) K)
    (hD : ∃ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0)
    (hgood : ∀ p : Space n d q J counts O,eval ((Module.finBasis K _).equivFun p) D≠0 →
      PrivatePositiveReduction p P) :
    ∃ D' : MvPolynomial (Fin (Module.finrank K
        (Space n d q J counts (fun j => (O j).map (rename e).toLinearMap)))) K,
      (∃ p : Space n d q J counts (fun j => (O j).map (rename e).toLinearMap),
        eval ((Module.finBasis K _).equivFun p) D'≠0) ∧
      ∀ p : Space n d q J counts (fun j => (O j).map (rename e).toLinearMap),
        eval ((Module.finBasis K _).equivFun p) D'≠0 → PrivatePositiveReduction p P' := by
  let F := outputRenameEquiv (n := n) (d := d) (q := q) (J := J) (counts := counts) (O := O) e
  obtain ⟨D',hD',hgood'⟩ := principal_open_linear_pullback F.symm.toLinearMap
    F.symm.surjective D hD (fun p => PrivatePositiveReduction p P) hgood
  refine ⟨D',hD',?_⟩
  intro p hp
  have H := private_positive_reduction_output_rename hd hO hJ e (F.symm p) P P' hP' (hgood' p hp)
  change PrivatePositiveReduction (F (F.symm p)) P' at H
  simpa only [LinearEquiv.apply_symm_apply] using H

end PreparedParameters
end Froberg
