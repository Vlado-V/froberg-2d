module

public import Froberg.GeneralOuterShadow
public import Froberg.BilinearScalarFamily
public import Froberg.IntermediateScalarBudget

@[expose] public section

/-! The new-layer quotient in B.4 has generically injective scalar action,
with an explicit sufficient finite budget. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
open Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Infinite K] [Fintype I] [DecidableEq I]
variable {n s d h q B : ℕ}

/-- B.11 plus the finite scalar budget supplies the actual incidence bound. -/
theorem intermediate_scalar_injective_of_budget
    (hn : 0<n) (hh : 0<h) (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i, (e i).degree=s)
    (hv : ∀ S : Finset I, S.card≤h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v) (hB : B≤h)
    (hsize : ∀ β : Exponent n (s+d), (labelsBelow e β.val).card≤B)
    (hcount : h*(s+d).choose s * (q+h*(n+s-1).choose s+(h*2^h)*(n+(d-1)-1).choose (d-1)) ≤
      (h-B)*(n+s+d-1).choose d) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → Forms K n d))) K,
      (∃ Q : Fin q → Forms K n d, eval (coordinates K _ Q) P ≠ 0) ∧
      ∀ Q : Fin q → Forms K n d, eval (coordinates K _ Q) P ≠ 0 →
        Function.Injective (BilinearScalarFamily.multiplication (quotientMultiply (d := d) e v he) Q) := by
  apply BilinearScalarFamily.generic_injective_of_shadow
  intro L
  let N := h*(n+s-1).choose s
  let E := (h*2^h)*(n+(d-1)-1).choose (d-1)
  let C := h*(s+d).choose s
  have hC : 0<C := Nat.mul_pos hh (Nat.choose_pos (by omega))
  have hdim : finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) ≤ N := by
    have ht := (relationSpace (d := 0) e v he).finrank_quotient_le
    simpa only [N,Nat.add_zero,Module.finrank_pi_fintype,finrank_forms K n s hn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using ht
  have hshadow := general_outer_shadow (d := d) e v hn he hv hm B hB hsize L
  have hc := (Nat.mul_le_mul_right (finrank K L) hcount).trans hshadow
  have hplain : (q+N)*finrank K L ≤ finrank K (outerImage (d := d) e v he L) := by
    apply Nat.le_of_mul_le_mul_left (c := C)
    · change C*((q+N)*finrank K L) ≤ C*finrank K (outerImage (d := d) e v he L)
      change C*(q+N+E)*finrank K L ≤ C*(finrank K (outerImage (d := d) e v he L)+E*finrank K L) at hc
      nlinarith
    · exact hC
  have hmin : min (finrank K L)
      (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)-finrank K L) ≤ finrank K L := min_le_left _ _
  change q*finrank K L + finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)*
    min (finrank K L) (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)-finrank K L) ≤ _
  calc
    _ ≤ q*finrank K L + N*finrank K L := Nat.add_le_add_left (Nat.mul_le_mul hdim hmin) _
    _ = (q+N)*finrank K L := by ring
    _ ≤ _ := hplain

end Froberg.AttachedMultiplication
