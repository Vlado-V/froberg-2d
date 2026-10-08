import Froberg.PrivateDetectedBoundary
import Froberg.PrivateBoundaryRemoval
import Froberg.IntrinsicBiformRow

/-! The first private coefficient row splits into its actual private Koszul
boundary and an ordinary scalar/new-layer relation. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {a z d b q m h c : ℕ}

 theorem first_private_intrinsic_row (hd : 3≤d)
    (bo : Basis (Fin h) K (homogeneousSubmodule σ K 1))
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (w : Fin b → Fin h → K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination (fun k => (bo k).val) (w i)*(bo j).val)=A i (Pi.single j 1))
    (hker : (privatePolynomialMap (a := a) (s := d-1) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := d-1) ι w))))
    (Q : Fin q → Forms K a d)
    (E : Fin m → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (hE : ∀ i,biformVectorDetector T (E i)=0)
    (x : Fin q → FullBiform K σ (a+z) 2 (d-2))
    (p : Fin m → Forms K (a+z) d)
    (u : Fin b → FullBiform K σ (a+z) 1 (d-1))
    (hrel : (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i).val)*(x i).val)+
      (∑ i,E i*rename Sum.inr (p i).val)+
      (∑ i,(rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)))*(u i).val)=0) :
    (fun i => (u i).val)∈Submodule.span K (Set.range (koszulVector
      (fun i => rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
        rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K))))) ∧
    (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i).val)*(x i).val)+
      (∑ i,E i*rename Sum.inr (p i).val)=0 := by
  let P := fun i => rename Sum.inl (outputCombination (fun k => (bo k).val) (w i))*
    rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K))
  have hdetect : biformVectorDetector T (∑ i,E i*rename Sum.inr (p i).val)=0 := by
    funext k
    simp only [map_sum,Finset.sum_apply]
    have ht (i) : biformVectorDetector T (E i*rename Sum.inr (p i).val) k=0 := by
      rw [mul_comm,biformVectorDetector_scalar_mul,hE]
      simp only [Pi.zero_apply,mul_zero]
    simp only [ht,Finset.sum_const_zero,Pi.zero_apply]
  have hu : ∀ i,(u i).val∈(polynomialFormVector (fun k => (bo k).val) (d-1)).range := by
    intro i
    rw [polynomialFormVector_range_basis]
    exact (u i).property
  have hboundary := private_first_row_boundary (s := d-1) (t := d-2) (by omega) (by omega)
    T (fun k => (bo k).val) w ι A hA hker (fun i => (Q i).val)
    (fun i => (x i).val) (homogeneousSubmodule σ K 2) (fun i => (x i).property)
    (∑ i,E i*rename Sum.inr (p i).val) hdetect (fun i => (u i).val) hu hrel
  refine ⟨hboundary,?_⟩
  obtain ⟨M,hM⟩ := exists_matrixBoundary_of_mem_koszul P (fun i => (u i).val) hboundary
  have hz : (∑ i,P i*(u i).val)=0 := by
    have hMi (i) : matrixBoundary P M i=(u i).val := congrFun hM i
    simpa only [hMi] using matrixBoundary_cycle P M
  change _+(∑ i,P i*(u i).val)=0 at hrel
  simpa only [hz,add_zero] using hrel

end Froberg
