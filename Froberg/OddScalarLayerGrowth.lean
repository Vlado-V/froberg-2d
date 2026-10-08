import Froberg.BiformDimensions
import Froberg.TwoFamilyAugmentedOpen
import Froberg.OddRowAugmentedBudget

/-! The non-top odd target quotients have uniform scalar growth on a
nonempty open of the original scalar/linear generator parameters. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module TensorProduct MvPolynomial Filter
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K]
variable {h n d b qS qO t : ℕ}

theorem odd_scalar_layer_growth_open (hh : 0<h) (hn : 0<n)
    (hb : 1≤b) (hbd : b≤d)
    (hcount :
      (qS+t+(h+b-1).choose b*(n+(d-b)-1).choose (d-b))*
        ((h+b-1).choose b*(n+(d-b)-1).choose (d-b))+
      (qO+(h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1))*
        ((h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1)) ≤
      (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b)) :
    ∃ D : MvPolynomial (Fin (finrank K
      ((Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)) ×
       (Fin qS → Forms K h 0 ⊗[K] Forms K n d)))) K,
      (∃ p : (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)) ×
        (Fin qS → Forms K h 0 ⊗[K] Forms K n d),
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)) ×
        (Fin qS → Forms K h 0 ⊗[K] Forms K n d),
        eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (twoFamilyMultiplication (K := K)
      (P₁ := Forms K h 1 ⊗[K] Forms K n (d-1))
      (P₂ := Forms K h 0 ⊗[K] Forms K n d)
      (V₁ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
      (V₂ := Forms K h b ⊗[K] Forms K n (d-b))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
          (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) (oddRowScalarAction (K := K) (h := h) (n := n) hbd) p) ∧
        ∀ L : Submodule K (Forms K h b ⊗[K] Forms K n (d-b)),
          t*finrank K L ≤ finrank K (Quartic.BilinearImage.image
            (scalarModulo (K := K)
      (P := Forms K h 0 ⊗[K] Forms K n d)
      (V := Forms K h b ⊗[K] Forms K n (d-b))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
      (U := (Fin qO → Forms K h (b-1) ⊗[K] Forms K n (d-b+1)) ×
        (Fin qS → Forms K h b ⊗[K] Forms K n (d-b)))
      (twoFamilyMultiplication (K := K)
      (P₁ := Forms K h 1 ⊗[K] Forms K n (d-1))
      (P₂ := Forms K h 0 ⊗[K] Forms K n d)
      (V₁ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
      (V₂ := Forms K h b ⊗[K] Forms K n (d-b))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
              (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) (oddRowScalarAction (K := K) (h := h) (n := n) hbd) p)
              (oddRowScalarAction (K := K) (h := h) (n := n) hbd)) L) := by
  apply two_family_augmentation_open (K := K)
    (P₁ := Forms K h 1 ⊗[K] Forms K n (d-1))
    (P₂ := Forms K h 0 ⊗[K] Forms K n d)
    (V₁ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
    (V₂ := Forms K h b ⊗[K] Forms K n (d-b))
    (W := Forms K h b ⊗[K] Forms K n (2*d-b))
    (q₁ := qO) (q₂ := qS) (t := t)
    (T := (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b))
    (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd)
    (oddRowScalarAction (K := K) (h := h) (n := n) hbd)
    (finrank_biform_pos hh hn (b-1) (d-b+1))
    (finrank_biform_pos hh hn b (d-b))
  · intro L
    simpa only [finrank_biform hh hn,oddRowLinearAction] using
      biformAction_growth (K := K) hh hn
        (a := 1) (b := b-1) (c := d-1) (e := d-b+1)
        (r := b) (t := 2*d-b) (by omega) (by omega) L
  · intro L
    simpa only [finrank_biform hh hn,oddRowScalarAction] using
      biformAction_growth (K := K) hh hn
        (a := 0) (b := b) (c := d) (e := d-b)
        (r := b) (t := 2*d-b) (by omega) (by omega) L
  · simpa only [finrank_biform hh hn,Nat.add_comm] using hcount

end Froberg
