module

public import Froberg.BilinearPostcompose
public import Froberg.TwoFamilyIntrinsicOpen
public import Froberg.TensorScalarGrowth

@[expose] public section

/-! The actual two-family map of C.9 after projecting the X factor. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module TensorProduct Quartic MvPolynomial
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K] {h m e b qF qS : ℕ}

def projectedTopLinearAction (P : Forms K h (1+e) →ₗ[K] (Fin b → K)) :
    (Forms K h 1 ⊗[K] Forms K m e) →ₗ[K]
      (Forms K h e ⊗[K] Forms K m 1) →ₗ[K]
        ((Fin b → K) ⊗[K] Forms K m (1+e)) :=
  tensorFormProduct ((gradedMultiplication (d := 1) (e := e)).compr₂ₛₗ P)

theorem projected_top_linear_growth (hh : 0 < h) (hm : 0 < m)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (L : Submodule K (Forms K h e ⊗[K] Forms K m 1)) :
    b*(m+(1+e)-1).choose (1+e)*finrank K L≤
      ((h+e-1).choose e*m)*finrank K (BilinearImage.image (K := K) (F := Forms K h 1 ⊗[K] Forms K m e) (V := Forms K h e ⊗[K] Forms K m 1) (W := (Fin b → K) ⊗[K] Forms K m (1+e)) (projectedTopLinearAction (K := K) (h := h) (m := m) (e := e) (b := b) P) L) := by
  have hg (S : Submodule K (Forms K h e)) : b*finrank K S≤
      (h+e-1).choose e*finrank K
        (BilinearImage.image ((gradedMultiplication (d := 1) (e := e)).compr₂ₛₗ P) S) := by
    rw [bilinearImage_postcompose]
    simpa only [finrank_forms K h e hh] using hP S
  have ht := tensorized_bilinear_growth (d := e)
    ((gradedMultiplication (d := 1) (e := e)).compr₂ₛₗ P) hm ((h+e-1).choose e) b hg L
  simpa only [projectedTopLinearAction,Nat.add_assoc,Nat.add_sub_cancel,Nat.choose_one_right] using ht

theorem projected_top_two_family_open (hh : 0 < h) (hm : 0 < m) (hb : 0 < b)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (hcount : (qF+(h+e-1).choose e*m)*((h+e-1).choose e*m)+(qS+b)*b≤
      b*(m+(1+e)-1).choose (1+e)) :
    ∃ D : MvPolynomial (Fin (finrank K
      ((Fin qF → Forms K h 1 ⊗[K] Forms K m e) × (Fin qS → Forms K m (1+e))))) K,
      (∃ p : (Fin qF → Forms K h 1 ⊗[K] Forms K m e) × (Fin qS → Forms K m (1+e)),
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : (Fin qF → Forms K h 1 ⊗[K] Forms K m e) × (Fin qS → Forms K m (1+e)),
        eval ((Module.finBasis K _).equivFun p) D≠0 →
        Function.Injective (twoFamilyMultiplication (K := K) (V₁ := Forms K h e ⊗[K] Forms K m 1) (V₂ := Fin b → K) (projectedTopLinearAction (K := K) (h := h) (m := m) (e := e) (b := b) P) (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e))) p) := by
  have hdim : finrank K (Forms K h e ⊗[K] Forms K m 1)=(h+e-1).choose e*m := by
    rw [Module.finrank_tensorProduct,finrank_forms K h e hh,finrank_forms K m 1 hm]
    simp
  apply two_family_generic_of_natural_growth (K := K)
    (P₁ := Forms K h 1 ⊗[K] Forms K m e) (P₂ := Forms K m (1+e))
    (V₁ := Forms K h e ⊗[K] Forms K m 1) (V₂ := Fin b → K)
    (W := (Fin b → K) ⊗[K] Forms K m (1+e))
    (q₁ := qF) (q₂ := qS) (T := b*(m+(1+e)-1).choose (1+e))
    (projectedTopLinearAction (K := K) (h := h) (m := m) (e := e) (b := b) P) (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e)))
  · rw [hdim]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) hm
  · simpa using hb
  · intro L
    rw [hdim]
    exact projected_top_linear_growth hh hm P hP L
  · intro L
    rw [tensorScalarProduct_finrank,finrank_forms K m (1+e) hm]
    simp [Nat.mul_assoc]
  · simpa only [hdim,Module.finrank_pi_fintype,finrank_self,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using hcount

end Froberg
