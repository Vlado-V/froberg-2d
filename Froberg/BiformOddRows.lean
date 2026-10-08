import Froberg.BiformDimensions

/-! Actual nonempty rank opens for the scalar-plus-linear higher odd rows.
Every dimension is the cardinality of the corresponding homogeneous monomials. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module TensorProduct MvPolynomial
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K]
variable {h n d b qS qO : ℕ}

/-- The ordinary scalar/linear odd row has maximal rank on a concrete
nonempty polynomial open in its actual two lists of biform coefficients. -/
theorem higher_odd_biform_open (hh : 0<h) (hn : 0<n)
    (hb : 1≤b) (hbd : b≤d)
    (hcount :
      (qS+(h+b-1).choose b*(n+(d-b)-1).choose (d-b))*
        ((h+b-1).choose b*(n+(d-b)-1).choose (d-b))+
      (qO+(h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1))*
        ((h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1)) ≤
      (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b)) :
    ∃ D : MvPolynomial (Fin (finrank K
      ((Fin qS → Forms K h 0 ⊗[K] Forms K n d) ×
       (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1))))) K,
      (∃ p : (Fin qS → Forms K h 0 ⊗[K] Forms K n d) ×
        (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)),
        eval ((Module.finBasis K ((Fin qS → Forms K h 0 ⊗[K] Forms K n d) ×
          (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)))).equivFun p) D≠0) ∧
      ∀ p : (Fin qS → Forms K h 0 ⊗[K] Forms K n d) ×
        (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)),
        eval ((Module.finBasis K ((Fin qS → Forms K h 0 ⊗[K] Forms K n d) ×
          (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)))).equivFun p) D≠0 →
        Function.Injective (twoFamilyMultiplication (K := K)
          (P₁ := Forms K h 0 ⊗[K] Forms K n d)
          (P₂ := Forms K h 1 ⊗[K] Forms K n (d-1))
          (V₁ := Forms K h b ⊗[K] Forms K n (d-b))
          (V₂ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
          (W := Forms K h b ⊗[K] Forms K n (2*d-b))
          (oddRowScalarAction (K := K) (h := h) (n := n) hbd)
          (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) p) := by
  apply two_family_generic_of_natural_growth (K := K)
    (P₁ := Forms K h 0 ⊗[K] Forms K n d)
    (P₂ := Forms K h 1 ⊗[K] Forms K n (d-1))
    (V₁ := Forms K h b ⊗[K] Forms K n (d-b))
    (V₂ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
    (W := Forms K h b ⊗[K] Forms K n (2*d-b))
    (T := (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b))
    (oddRowScalarAction (K := K) (h := h) (n := n) hbd)
    (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd)
    (finrank_biform_pos (K := K) hh hn b (d-b))
    (finrank_biform_pos (K := K) hh hn (b-1) (d-b+1))
  · intro L
    simpa only [finrank_biform hh hn,oddRowScalarAction] using
      biformAction_growth (K := K) hh hn
        (a := 0) (b := b) (c := d) (e := d-b)
        (r := b) (t := 2*d-b) (by omega) (by omega) L
  · intro L
    simpa only [finrank_biform hh hn,oddRowLinearAction] using
      biformAction_growth (K := K) hh hn
        (a := 1) (b := b-1) (c := d-1) (e := d-b+1)
        (r := b) (t := 2*d-b) (by omega) (by omega) L
  · simpa only [finrank_biform hh hn] using hcount

/-- The corresponding one-family budget for the final scalar-free odd row. -/
theorem single_family_generic_of_natural_growth
    {F V W : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {q T : ℕ} (mu : F →ₗ[K] V →ₗ[K] W)
    (hV : 0<finrank K V)
    (hgrowth : ∀ L : Submodule K V,
      T*finrank K L≤finrank K V*finrank K (Quartic.BilinearImage.image mu L))
    (hcount : (q+finrank K V)*finrank K V≤T) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → F))) K,
      (∃ p : Fin q → F,eval (Quartic.PolynomialBilinearCoordinates.coordinates K _ p) D≠0) ∧
      ∀ p : Fin q → F,eval (Quartic.PolynomialBilinearCoordinates.coordinates K _ p) D≠0 →
        Function.Injective (BilinearScalarFamily.multiplication mu p) := by
  apply BilinearScalarFamily.generic_injective_of_shadow mu
  intro L
  apply Nat.le_of_mul_le_mul_left _ hV
  have hmin : min (finrank K L) (finrank K V-finrank K L)≤finrank K L := min_le_left _ _
  calc
    finrank K V*(q*finrank K L+finrank K V*min (finrank K L) (finrank K V-finrank K L))
        ≤finrank K V*((q+finrank K V)*finrank K L) := by
          apply Nat.mul_le_mul_left
          calc
            q*finrank K L+finrank K V*min (finrank K L) (finrank K V-finrank K L)
                ≤q*finrank K L+finrank K V*finrank K L :=
              Nat.add_le_add_left (Nat.mul_le_mul_left _ hmin) _
            _ =(q+finrank K V)*finrank K L := by ring
    _ ≤T*finrank K L := by
      calc
        _ =((q+finrank K V)*finrank K V)*finrank K L := by ring
        _ ≤T*finrank K L := Nat.mul_le_mul_right _ hcount
    _ ≤finrank K V*finrank K (Quartic.BilinearImage.image mu L) := hgrowth L

/-- The last odd row has only linear-output generators and constant scalar
coefficients, so its open follows from the one-family natural budget. -/
theorem upper_odd_biform_open (hh : 0<h) (hn : 0<n) (hd : 1≤d)
    (hcount : (qO+(h+d-1).choose d)*(h+d-1).choose d≤
      (h+(d+1)-1).choose (d+1)*(n+(d-1)-1).choose (d-1)) :
    ∃ D : MvPolynomial (Fin (finrank K
      (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)))) K,
      (∃ p : Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1),
        eval (Quartic.PolynomialBilinearCoordinates.coordinates K _ p) D≠0) ∧
      ∀ p : Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1),
        eval (Quartic.PolynomialBilinearCoordinates.coordinates K _ p) D≠0 →
        Function.Injective (BilinearScalarFamily.multiplication (K := K)
          (F := Forms K h 1 ⊗[K] Forms K n (d-1))
          (V := Forms K h d ⊗[K] Forms K n 0)
          (W := Forms K h (d+1) ⊗[K] Forms K n (d-1))
          (biformAction (K := K) (h := h) (n := n) (a := 1) (b := d) (c := d-1) (e := 0)
            (r := d+1) (t := d-1) (by omega) (by omega)) p) := by
  apply single_family_generic_of_natural_growth (K := K)
    (F := Forms K h 1 ⊗[K] Forms K n (d-1))
    (V := Forms K h d ⊗[K] Forms K n 0)
    (W := Forms K h (d+1) ⊗[K] Forms K n (d-1))
    (T := (h+(d+1)-1).choose (d+1)*(n+(d-1)-1).choose (d-1))
    (biformAction (K := K) (h := h) (n := n) (a := 1) (b := d)
      (c := d-1) (e := 0) (r := d+1) (t := d-1) (by omega) (by omega))
    (finrank_biform_pos (K := K) hh hn d 0)
  · intro L
    simpa only [finrank_biform hh hn] using biformAction_growth (K := K) hh hn
      (a := 1) (b := d) (c := d-1) (e := 0)
      (r := d+1) (t := d-1) (by omega) (by omega) L
  · simpa only [finrank_biform hh hn,Nat.choose_zero_right,mul_one] using hcount

end Froberg
