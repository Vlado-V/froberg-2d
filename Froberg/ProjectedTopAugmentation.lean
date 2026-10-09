module

public import Froberg.ProjectedTopGeneric
public import Froberg.TwoFamilyAugmentedOpen

@[expose] public section

/-! The actual top row admits, on one principal open in its original
parameters, both injectivity and the scalar quotient-growth estimate. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Filter Module TensorProduct MvPolynomial Quartic
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K] {h m e b qF qS t : ℕ}

abbrev projectedTopMap (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (p : ProjectedTopParameters K h m e qF qS) :=
  twoFamilyMultiplication (K := K)
    (V₁ := Forms K h e ⊗[K] Forms K m 1) (V₂ := Fin b → K)
    (projectedTopLinearAction (m := m) P)
    (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e))) p

abbrev projectedTopScalarAction (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (p : ProjectedTopParameters K h m e qF qS) :=
  scalarModulo (K := K) (P := Forms K m (1+e)) (V := Fin b → K)
    (W := (Fin b → K) ⊗[K] Forms K m (1+e))
    (U := (Fin qF → Forms K h e ⊗[K] Forms K m 1) × (Fin qS → Fin b → K))
    (projectedTopMap P p)
    (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e)))

def ProjectedTopGrowthOpen (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (m qF qS t : ℕ) : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (ProjectedTopParameters K h m e qF qS))) K,
    (∃ p : ProjectedTopParameters K h m e qF qS,
      eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p : ProjectedTopParameters K h m e qF qS,
      eval ((Module.finBasis K _).equivFun p) D≠0 →
      Function.Injective (projectedTopMap P p) ∧
      ∀ L : Submodule K (Fin b → K),
        t*finrank K L≤finrank K (BilinearImage.image (projectedTopScalarAction P p) L)

theorem projected_top_growth_open (hh : 0 < h) (hm : 0 < m) (hb : 0 < b)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (hcount : (qF+(h+e-1).choose e*m)*((h+e-1).choose e*m)+(qS+t+b)*b≤
      b*(m+(1+e)-1).choose (1+e)) :
    ProjectedTopGrowthOpen P m qF qS t := by
  have hdim : finrank K (Forms K h e ⊗[K] Forms K m 1)=(h+e-1).choose e*m := by
    rw [Module.finrank_tensorProduct,finrank_forms K h e hh,finrank_forms K m 1 hm]
    simp
  apply two_family_augmentation_open (K := K)
    (P₁ := Forms K h 1 ⊗[K] Forms K m e) (P₂ := Forms K m (1+e))
    (V₁ := Forms K h e ⊗[K] Forms K m 1) (V₂ := Fin b → K)
    (W := (Fin b → K) ⊗[K] Forms K m (1+e))
    (q₁ := qF) (q₂ := qS) (t := t) (T := b*(m+(1+e)-1).choose (1+e))
    (projectedTopLinearAction (m := m) P)
    (tensorScalarProduct (K := K) (V := Fin b → K) (P := Forms K m (1+e)))
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

theorem eventually_projected_top_growth_open (hh : 0 < h) (he : 2≤e) (hb : 0 < b)
    (P : Forms K h (1+e) →ₗ[K] (Fin b → K))
    (hP : ∀ L : Submodule K (Forms K h e),b*finrank K L≤
      finrank K (Forms K h e)*
        finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P))
    (hratio : (h : ℝ)/(2*((1+e : ℕ) : ℝ))≤(b : ℝ)/((h+e-1).choose e : ℝ))
    (qF qS : ℕ → ℕ)
    (hF : Tendsto (fun m : ℕ => (qF m : ℝ)/(m : ℝ)^e) atTop
      (𝓝 ((h : ℝ)*criticalRatio (1+e)/(e.factorial : ℝ))))
    (hS : Tendsto (fun m : ℕ => (qS m : ℝ)/(m : ℝ)^(1+e)) atTop
      (𝓝 (criticalRatio (1+e)/((1+e).factorial : ℝ)))) :
    ∀ᶠ m : ℕ in atTop,
      ProjectedTopGrowthOpen P m (qF m) (qS m) (scalarReserveCount (1+e) m) := by
  have hbudget := eventually_augmented_top_budget (show 3≤1+e by omega)
    (Nat.choose_pos (show e≤h+e-1 by omega)) hb hratio qF qS
    (by simpa only [show 1+e-1=e by omega] using hF) hS
  filter_upwards [hbudget,eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  exact projected_top_growth_open hh hmpos hb P hP hm

end Froberg
