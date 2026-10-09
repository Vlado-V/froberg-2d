module

public import Froberg.PrivateOutputMatrices
public import Froberg.PrivateAvoidance
public import Froberg.ExtendedMixedRow

@[expose] public section

/-! The actual scalar-plus-existing-product residual automatically avoids
private powers in every later coefficient row. -/
noncomputable section
namespace Froberg
open Module MvPolynomial PrivateColumns Quartic.FreeCoefficients
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} {a z s b h c m q r t : ℕ}

/-- Core scalar products with lower-degree arbitrary private coefficients,
and arbitrary core-only products, cannot contain a private power. -/
theorem mixed_residual_avoids_private_powers (hs : 0<s) (ht : t<s)
    (ι : Fin b ↪ Fin z) (Q : Fin q → Poly K a)
    (x : Fin q → Fin c → Forms K (a+z) t) (C : Fin c → Poly K a) :
    avoidsPrivatePowers (s := s) ι (fun k =>
      (∑ i,rename (Fin.castAdd z) (Q i)*(x i k).val)+rename (Fin.castAdd z) (C k)) := by
  apply avoidsPrivatePowers_of_free_degree_lt
  intro k β hβ
  have hbn : β≠0 := by intro h; subst β; simpa using (not_le_of_gt hs hβ)
  have hx (i) : freeCoeff β (x i k).val=0 :=
    freeCoeff_eq_zero_of_degree_lt _ (x i k).property β (by omega)
  simp only [map_add,map_sum,freeCoeff_rename_mul,hx,mul_zero,Finset.sum_const_zero,
    freeCoeff_rename_core,if_neg hbn,add_zero]

/-- Every later private coefficient is zero in the literal mixed row. The
only rank hypothesis concerns the same chosen sparse E family modulo each
private output image. -/
theorem private_mixed_polynomial_row_zero
    (hs : 2 ≤ s) (hr : r<s) (ht : t<s)
    (o : Fin c → MvPolynomial σ K) (ho : LinearIndependent K o)
    (u : Fin h → MvPolynomial σ K) (hu : LinearIndependent K u)
    (w : Fin b → MvPolynomial σ K) (hw : ∀ i,w i≠0)
    (ι : Fin b ↪ Fin z)
    (A : Fin b → (Fin h → K) →ₗ[K] (Fin c → K))
    (hA : ∀ i j,outputCombination o (A i (Pi.single j 1))=w i*u j)
    (e : Fin m → Fin a →₀ ℕ) (v : Fin m → Fin c → K)
    (hprojected : ∀ j d,d≤1 → ∀ p : Fin m → Forms K a d,
      (∀ α,sparseOutputCoefficient e v p α∈(A j).range) → p=0)
    (Q : Fin q → Poly K a) (x : Fin q → Fin c → Forms K (a+z) t)
    (C : Fin c → Poly K a)
    (p : Fin m → Forms K (a+z) (s+1))
    (zeta : Fin b → Fin h → Forms K (a+z) r)
    (hrel : (∑ i,polynomialVector o (fun k =>
        rename (Fin.castAdd z) (monomial (e i) (v i k)))*rename Sum.inr (p i).val)+
      (∑ i,(rename Sum.inl (w i)*rename Sum.inr (monomial (privateExponent a s ι i) (1:K)))*
        polynomialVector u (fun j => (zeta i j).val))+
      polynomialVector o (fun k =>
        (∑ i,rename (Fin.castAdd z) (Q i)*(x i k).val)+rename (Fin.castAdd z) (C k))=0) :
    zeta=0 := by
  exact private_polynomial_row_lower_zero hs hr o ho u hu w hw ι A hA e v hprojected p zeta _
    (mixed_residual_avoids_private_powers (by omega) ht ι Q x C) hrel

end Froberg
