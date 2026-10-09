module

public import Froberg.VectorExpansionOpen
public import Quartic.QuotientBilinearImage

@[expose] public section

/-! Relative openness for actual homogeneous polynomial quotient presentations. -/
noncomputable section
namespace Froberg.VectorExpansionOpen
open Module MvPolynomial VectorMultiplicationCoordinates Quartic
open HomogeneousCoefficientCoordinates
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {h m c s t : ℕ} {I A : Type*} [Fintype A]

lemma polynomial_tupleMap
    (g : (I → K) → Fin c → Rows K h m s)
    (hg : ∀ j,IsPolynomialFamily (fun p => g p j)) :
    IsPolynomialFamily (fun p => BilinearImage.tupleMap (multiplication (d := t)) (g p)) := by
  apply isPolynomialFamily_linearMap
  intro f
  have hp := IsPolynomialFamily.sum (fun j => (hg j).linear_comp (multiplication (f j)))
  simpa only [BilinearImage.tupleMap_apply] using hp

lemma product_span_dimension (g : Fin c → Rows K h m s)
    (hg : Function.Injective (BilinearImage.tupleMap (multiplication (d := t)) g)) :
    finrank K (BilinearImage.image (multiplication (d := t)) (Submodule.span K (Set.range g))) =
      c*FormCount m t := by
  rw [← BilinearImage.range_tupleMap,LinearMap.finrank_range_of_inj hg]
  have hf : finrank K (Forms K m t)=FormCount m t := by
    calc
      finrank K (Forms K m t)=finrank K (Fin (FormCount m t) → K) := finiteEquiv.finrank_eq
      _=FormCount m t := by simp
  simp only [Module.finrank_pi_fintype,hf,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

/-- All finitely many quotient growth bounds persist in one polynomial
neighborhood of a geometric witness, together with the exact source and
relation dimensions. -/
theorem quotient_principal_open [IsAlgClosed L]
    (g : (I → K) → Fin c → Rows K h m s)
    (hg : ∀ j,IsPolynomialFamily (fun p => g p j)) (p₀ : I → K)
    (hsource : LinearIndependent K (g p₀))
    (htarget : Function.Injective (BilinearImage.tupleMap (multiplication (d := t)) (g p₀)))
    (ell bound : A → ℕ) (hell : ∀ i,0 < ell i+c)
    (hwitness : ∀ i,Expands (fun j => mapRows (L := L) (g p₀ j)) t
      (ell i+c) (bound i+c*FormCount m t)) :
    ∃ D : MvPolynomial I K,eval p₀ D ≠ 0 ∧ ∀ p : I → K,eval p D ≠ 0 →
      LinearIndependent K (g p) ∧
      Function.Injective (BilinearImage.tupleMap (multiplication (d := t)) (g p)) ∧
      ∀ i (U : Submodule K ((Rows K h m s) ⧸ Submodule.span K (Set.range (g p)))),
        finrank K U=ell i → bound i ≤ finrank K (BilinearImage.image
          (QuotientBilinearImage.quotientMap (multiplication (d := t))
            (Submodule.span K (Set.range (g p)))) U) := by
  obtain ⟨D₁,hD₁,h₁⟩ := independent_polynomial_principal_open
    (fun j p => g p j) hg p₀ hsource
  obtain ⟨D₂,hD₂,h₂⟩ := injective_polynomial_principal_open
    (fun p => BilinearImage.tupleMap (multiplication (d := t)) (g p)) (polynomial_tupleMap g hg) p₀ htarget
  obtain ⟨D₃,hD₃,h₃⟩ := principal_open_finite g hg p₀
    (fun i => ell i+c) (fun i => bound i+c*FormCount m t) hell hwitness
  refine ⟨D₁*D₂*D₃,by simpa only [map_mul] using mul_ne_zero (mul_ne_zero hD₁ hD₂) hD₃,?_⟩
  intro p hp
  have hp' : eval p D₁ ≠ 0 ∧ eval p D₂ ≠ 0 ∧ eval p D₃ ≠ 0 := by
    simpa only [map_mul,mul_ne_zero_iff,and_assoc] using hp
  have hi := h₁ p hp'.1
  have hj := h₂ p hp'.2.1
  refine ⟨hi,hj,?_⟩
  intro i U hU
  have hdE : finrank K (Submodule.span K (Set.range (g p)))=c := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hi
  have hdR := product_span_dimension (g p) hj
  apply (QuotientBilinearImage.expansion_iff_ambient (multiplication (d := t))
    (Submodule.span K (Set.range (g p))) (ell i) (bound i)).mpr ?_ U hU
  intro S hES hS
  rw [hdE] at hS
  rw [hdR]
  exact h₃ p hp'.2.2 i S hES hS

end Froberg.VectorExpansionOpen
