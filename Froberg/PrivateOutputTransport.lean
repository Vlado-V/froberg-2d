module

public import Froberg.PrivateSparseSeparation
public import Froberg.PolynomialOutputImage
public import Froberg.HomogeneousOutputCoordinates

@[expose] public section

/-! The coordinate private maps are exactly multiplication by the literal
private-power generators after transporting their output coordinates. -/
noncomputable section
namespace Froberg
open Module MvPolynomial PrivateColumns AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {a z s b h c t : ℕ}

/-- Exact transport of every private column, with the same coefficient tuple
and private variable as in the coordinate separation theorem. -/
theorem private_output_transport
    (o : Fin c → MvPolynomial σ K) (u : Fin h → MvPolynomial σ K)
    (w : Fin b → MvPolynomial σ K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,outputCombination o (A i (Pi.single j 1))=w i*u j)
    (v : Fin b → Fin h → Forms K (a+z) t) :
    polynomialVector o (privatePolynomialMapAt (s := s) ι A v)=
      ∑ i,(rename Sum.inl (w i)*rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*
        polynomialVector u (fun j => (v i j).val) := by
  have hmaps : privatePolynomialMapAt (s := s) ι A v=
      ∑ i,AttachedMultiplication.multiplication
        (fun _ : Fin h => privateExponent a s ι i)
        (fun j => A i (Pi.single j 1)) (v i) := by
    funext k
    simp only [privatePolynomialMapAt,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,AttachedMultiplication.multiplication_apply]
  rw [hmaps,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←attachedPolynomialFamily_multiplication]
  simp only [attachedPolynomialFamily_factor,hA,map_mul,polynomialVector_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The output map is injective whenever multiplication by the chosen
nonzero output form is injective and the lower output basis is independent. -/
theorem private_output_map_injective
    (o : Fin c → MvPolynomial σ K) (u : Fin h → MvPolynomial σ K)
    (hu : LinearIndependent K u) (w : MvPolynomial σ K) (hw : w≠0)
    (A : (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ j,outputCombination o (A (Pi.single j 1))=w*u j) :
    Function.Injective A := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hcomb : outputCombination o (A v)=w*outputCombination u v := by
    have heq : v=∑ j,v j • Pi.single j 1 := by
      classical
      funext j
      simp [Pi.single_apply]
    calc
      outputCombination o (A v) = ∑ j,v j • outputCombination o (A (Pi.single j 1)) := by
        conv_lhs => rw [heq]
        simp only [map_sum,map_smul]
      _ = ∑ j,v j • (w*u j) := by simp_rw [hA]
      _ = w*outputCombination u v := by
        simp only [outputCombination,LinearMap.coe_mk,AddHom.coe_mk,
          Finset.mul_sum,mul_smul_comm]
  rw [hv,map_zero] at hcomb
  have hz : outputCombination u v=0 := (mul_eq_zero.mp hcomb.symm).resolve_left hw
  funext i
  exact Fintype.linearIndependent_iff.mp hu v hz i

/-- Core polynomial matrices commute with faithful output transport even
after adjoining private variables. -/
theorem extended_matrix_output_transport {m : ℕ}
    (o : Fin c → MvPolynomial σ K) (E : Fin c → Fin m → Poly K a)
    (p : Fin m → Forms K (a+z) t) :
    polynomialVector o (extendedCorePolynomialMatrix E p)=
      ∑ i,polynomialVector o (fun k => rename (Fin.castAdd z) (E k i))*
        rename Sum.inr (p i).val := by
  simp only [polynomialVector_apply,extendedCorePolynomialMatrix,LinearMap.coe_mk,
    AddHom.coe_mk,map_sum,map_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Literal polynomial form of the later private-row separation. All sparse
and private coefficient tuples are unchanged by the coordinate transport. -/
theorem private_polynomial_row_image_zero {m r : ℕ}
    (hs : 2 ≤ s)
    (o : Fin c → MvPolynomial σ K) (ho : LinearIndependent K o)
    (u : Fin h → MvPolynomial σ K)
    (w : Fin b → MvPolynomial σ K) (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,outputCombination o (A i (Pi.single j 1))=w i*u j)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hprojected : ∀ j d,d≤1 → ∀ p : Fin m → Forms K a d,
      (∀ α,sparseOutputCoefficient e v p α∈(A j).range) → p=0)
    (p : Fin m → Forms K (a+z) (s+1))
    (zeta : Fin b → Fin h → Forms K (a+z) r)
    (res : Fin c → Poly K (a+z))
    (hres : avoidsPrivatePowers (s := s) ι res)
    (hrel : (∑ i,polynomialVector o (fun k =>
        rename (Fin.castAdd z) (monomial (e i) (v i k)))*rename Sum.inr (p i).val)+
      (∑ i,(rename Sum.inl (w i)*rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*
        polynomialVector u (fun j => (zeta i j).val))+polynomialVector o res=0) :
    privatePolynomialMapAt (s := s) ι A zeta=0 := by
  apply private_sparse_separation hs ι A e v hprojected p zeta res hres
  apply polynomialVector_injective o ho
  rw [map_zero,map_add,map_add,extended_matrix_output_transport,
    private_output_transport o u w ι A hA]
  exact hrel

/-! Below the private endpoint, the separated private image has zero kernel. -/
theorem private_polynomial_row_lower_zero {m r : ℕ}
    (hs : 2 ≤ s) (hr : r<s)
    (o : Fin c → MvPolynomial σ K) (ho : LinearIndependent K o)
    (u : Fin h → MvPolynomial σ K) (hu : LinearIndependent K u)
    (w : Fin b → MvPolynomial σ K) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,outputCombination o (A i (Pi.single j 1))=w i*u j)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hprojected : ∀ j d,d≤1 → ∀ p : Fin m → Forms K a d,
      (∀ α,sparseOutputCoefficient e v p α∈(A j).range) → p=0)
    (p : Fin m → Forms K (a+z) (s+1))
    (zeta : Fin b → Fin h → Forms K (a+z) r)
    (res : Fin c → Poly K (a+z))
    (hres : avoidsPrivatePowers (s := s) ι res)
    (hrel : (∑ i,polynomialVector o (fun k =>
        rename (Fin.castAdd z) (monomial (e i) (v i k)))*rename Sum.inr (p i).val)+
      (∑ i,(rename Sum.inl (w i)*rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*
        polynomialVector u (fun j => (zeta i j).val))+polynomialVector o res=0) :
    zeta=0 := by
  apply private_sparse_lower_zero hs hr ι A
    (fun i => private_output_map_injective o u hu (w i) (hw i) (A i) (hA i))
    e v hprojected p zeta res hres
  apply polynomialVector_injective o ho
  rw [map_zero,map_add,map_add,extended_matrix_output_transport,
    private_output_transport o u w ι A hA]
  exact hrel

end Froberg
