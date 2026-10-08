import Froberg.BiformVectorDetector
import Froberg.PrivateBoundaryTransport

/-! In the first positive even row, the actual output detector turns the
private coefficient into a literal constant private Koszul boundary. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {a z s b h c q t : ℕ}

theorem biformVectorDetector_private
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (o : Fin h → MvPolynomial σ K) (w : Fin b → MvPolynomial σ K)
    (ι : Fin b ↪ Fin z) (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (w i*o j)=A i (Pi.single j 1))
    (v : Fin b → Fin h → Forms K (a+z) s) :
    biformVectorDetector T (∑ i,(rename Sum.inl (w i)*
      rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*polynomialFormVector o s (v i))=
      privatePolynomialMap ι A v := by
  funext k
  simp only [map_sum,Finset.sum_apply,privatePolynomialMap,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  change biformVectorDetector T ((rename Sum.inl (w i)*
    rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*
      polynomialVector o (fun j => (v i j).val)) k=_
  rw [polynomialVector_apply,Finset.mul_sum,map_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have he : (rename Sum.inl (w i)*rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*
      (rename Sum.inl (o j)*rename Sum.inr (v i j).val)=
      rename Sum.inl (w i*o j)*rename Sum.inr
        (monomial (privateExponent a s ι i) (1:K)*(v i j).val) := by
    simp only [map_mul]
    ring
  rw [he,biformVectorDetector_tmul,hA]
  rw [←smul_mul_assoc,smul_monomial,smul_eq_mul,mul_one]

/-- A literal polynomial row has a constant private Koszul boundary whenever
its nonprivate quadratic-output term is killed by the selected detector. -/
theorem private_first_row_boundary
    (hs : 2 ≤ s) (ht : t<s)
    (T : MvPolynomial σ K →ₗ[K] (Fin c → K))
    (o : Fin h → MvPolynomial σ K) (w : Fin b → Fin h → K)
    (ι : Fin b ↪ Fin z) (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,T (outputCombination o (w i)*o j)=A i (Pi.single j 1))
    (hker : (privatePolynomialMap (a := a) (s := s) ι A).ker=
      Submodule.span K (Set.range (koszulVector (privateGenerator (a := a) (s := s) ι w))))
    (Q : Fin q → Poly K a)
    (x : Fin q → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (O : Submodule K (MvPolynomial σ K))
    (hx : ∀ i,x i∈biformImage O (Forms K (a+z) t))
    (C : MvPolynomial (σ ⊕ Fin (a+z)) K) (hC : biformVectorDetector T C=0)
    (u : Fin b → MvPolynomial (σ ⊕ Fin (a+z)) K)
    (hu : ∀ i,u i∈(polynomialFormVector o s).range)
    (hrel : (∑ i,rename Sum.inr (rename (Fin.castAdd z) (Q i))*x i)+C+
      (∑ i,(rename Sum.inl (outputCombination o (w i))*
        rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*u i)=0) :
    u∈Submodule.span K (Set.range (koszulVector
      (fun i => rename Sum.inl (outputCombination o (w i))*
        rename Sum.inr (monomial (privateExponent a s ι i) (1:K))))) := by
  choose v hv using hu
  let xp : Fin q → Fin c → Forms K (a+z) t := fun i k =>
    ⟨biformVectorDetector T (x i) k,biformVectorDetector_homogeneous T O (hx i) k⟩
  let res : Fin c → Poly K (a+z) := fun k => ∑ i,rename (Fin.castAdd z) (Q i)*(xp i k).val
  have hres : avoidsPrivatePowers (s := s) ι res := by
    simpa only [map_zero,add_zero] using mixed_residual_avoids_private_powers
      (by omega : 0<s) ht ι Q xp (fun _ => 0)
  have hrow : privatePolynomialMap ι A v+res=0 := by
    have hr := congrArg (biformVectorDetector T) hrel
    have hp : (∑ i,(rename Sum.inl (outputCombination o (w i))*
        rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*u i)=
        ∑ i,(rename Sum.inl (outputCombination o (w i))*
        rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*polynomialFormVector o s (v i) := by
      simp only [hv]
    rw [hp,map_add,map_add,hC,add_zero,map_zero,biformVectorDetector_private T o
      (fun i => outputCombination o (w i)) ι A hA] at hr
    funext k
    have hk := congrFun hr k
    simpa only [map_sum,Finset.sum_apply,biformVectorDetector_scalar_mul,Pi.add_apply,
      Pi.zero_apply,xp,res,add_comm] using hk
  have hz : privatePolynomialMap ι A v=0 := by
    apply private_sparse_separation (m := 0) hs ι A Fin.elim0 Fin.elim0
      (fun _ _ _ p _ => Subsingleton.elim p 0) Fin.elim0 v res hres
    funext k
    simpa only [extendedCorePolynomialMatrix,LinearMap.coe_mk,AddHom.coe_mk,
      Fin.sum_univ_zero,Pi.zero_apply,Pi.add_apply,zero_add,
      privatePolynomialMapAt,privatePolynomialMap] using congrFun hrow k
  have hh := private_boundary_polynomial o ι A w hker v hz
  simpa only [hv] using hh

end Froberg
