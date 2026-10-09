module

public import Froberg.IntrinsicSecondStage
public import Froberg.AffineSharedPolynomial
public import Froberg.IntrinsicAffineNormalization
public import Froberg.FreezeParameters

@[expose] public section

/-! The common-scalar second stage of the layered covector argument. Every
fixed positive component is retained. Auxiliary cuts are fixed once, and
only the actual scalar family remains as the final open parameter. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.BilinearCovectorCharts Quartic.BilinearCoefficientKernel
variable {K X U : Type*} [Field K] [Infinite K] [IsAlgClosed K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable {q₀ N s₀ nf r a b T q s k : ℕ}

/-- On each normalized closed bottom chart, a first-stage rank bound and
the exact shared-scalar budget give fixed cuts and a nonempty scalar-only
open. The first vector and all graph coordinates remain universal. -/
theorem affine_layered_covectors_joint
    (degrees : Fin nf → ℕ) (f : ∀ i,Forms K q₀ (degrees i))
    (ell : Fin (s₀+1) → Forms K q₀ 1)
    (hempty : ∀ t : Fin q₀ → K,(∀ i,eval t (f i).val=0) →
      (∀ j,eval t (ell j).val=0) → t=0)
    (A : (Fin (q₀+N) → K) → X →ₗ[K] U)
    (lambda : (Fin (q₀+N) → K) → X → (Fin T → K))
    (hA : IsPolynomialFamily A)
    (hlambda : IsPolynomialFamily (fun p : (Fin (q₀+N) ⊕ Fin (finrank K X)) → K =>
      lambda (fun i => p (.inl i)) ((Module.finBasis K X).equivFun.symm (fun i => p (.inr i)))))
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (hcount : s₀+N+finrank K X<r+q*(a-k)+s) :
    ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 →
      ∀ (x : X) (t : Fin q₀ → K),
        (∀ i,eval t (f i).val=0) → eval t (ell 0).val=1 → ∀ u : Fin N → K,
        r≤finrank K (A (Fin.append t u)).range →
        lambda (Fin.append t u) x≠0 →
        finrank K (relationMap mu (lambda (Fin.append t u) x)).ker≤k →
        A (Fin.append t u) x=0 →
        ¬ ((∀ i v,covector (lambda (Fin.append t u) x) (mu (y.1 i) v+B i v)=0) ∧
          (∀ j,covector (lambda (Fin.append t u) x) (y.2 j)=0)) := by
  let C := fun p x => affineSharedConstraint (s := s) mu B (lambda p x)
  have hC : IsPolynomialFamily (fun p : (Fin (q₀+N) ⊕ Fin (finrank K X)) → K =>
      C (fun i => p (.inl i)) ((Module.finBasis K X).equivFun.symm (fun i => p (.inr i)))) :=
    affineSharedConstraint_polynomial mu B _ hlambda
  have hempty' : ∀ t : Fin q₀ → K,(∀ i,aeval t (f i).val=0) →
      (∀ j,aeval t (ell j).val=0) → t=0 := by
    simpa only [aeval_eq_eval] using hempty
  obtain ⟨P,hP,hgood⟩ := intrinsic_second_stage_with_parameters
    (L := K) degrees f ell hempty' A C hA hC (by omega : s₀+N+finrank K X<r+(q*(a-k)+s))
  let Good : SharedCovectorPolynomial.Input K b T q s × K → Prop := fun y =>
    ∀ (x : X) (t : Fin q₀ → K),
      (∀ i,eval t (f i).val=0) → eval t (ell 0).val=1 → ∀ u : Fin N → K,
      r≤finrank K (A (Fin.append t u)).range →
      lambda (Fin.append t u) x≠0 →
      finrank K (relationMap mu (lambda (Fin.append t u) x)).ker≤k →
      A (Fin.append t u) x=0 → C (Fin.append t u) x y≠0
  have hGP : ∀ z,eval z P≠0 → Good ((Module.finBasis K _).equivFun.symm z) := by
    intro z hz x t hf ht u hr hne hk hzero
    have hR : q*(a-k)+s≤finrank K (C (Fin.append t u) x).range := by
      apply le_trans _ (affineSharedConstraint_rank mu B _ hne)
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left q (by omega)
    exact (hgood z hz x t hf ht u hr hR).resolve_left (not_not.mpr hzero)
  have hscale : ∀ c : K,c≠0 → ∀ y,Good (c • y) → Good y := by
    intro c _ y hy x t hf ht u hr hne hk hzero hz
    apply hy x t hf ht u hr hne hk hzero
    rw [map_smul,hz,smul_zero]
  obtain ⟨P₁,hP₁,hgood₁⟩ := intrinsic_principal_open_affine_normalization P hP Good hGP hscale
  have hP₁' : ∃ y : SharedCovectorPolynomial.Input K b T q s,
      eval ((Module.finBasis K _).equivFun y) P₁≠0 := by
    obtain ⟨y,hy⟩ := hP₁
    exact ⟨(Module.finBasis K _).equivFun.symm y,by simpa only [LinearEquiv.apply_symm_apply] using hy⟩
  have hgood₁' : ∀ y : SharedCovectorPolynomial.Input K b T q s,
      eval ((Module.finBasis K _).equivFun y) P₁≠0 → Good (y,1) := by
    intro y hy
    simpa only [LinearEquiv.symm_apply_apply] using hgood₁ _ hy
  refine ⟨P₁,hP₁',?_⟩
  intro y hy x t hf ht u hr hne hk hzero hjoint
  exact hgood₁' y hy x t hf ht u hr hne hk hzero
    ((affineSharedConstraint_kernel_iff mu B _ y).mpr hjoint)

/-- Fix the auxiliary cuts only after the desired joint parameter open is formed. -/
theorem affine_layered_covectors_avoid
    (degrees : Fin nf → ℕ) (f : ∀ i,Forms K q₀ (degrees i))
    (ell : Fin (s₀+1) → Forms K q₀ 1)
    (hempty : ∀ t : Fin q₀ → K,(∀ i,eval t (f i).val=0) →
      (∀ j,eval t (ell j).val=0) → t=0)
    (A : (Fin (q₀+N) → K) → X →ₗ[K] U)
    (lambda : (Fin (q₀+N) → K) → X → (Fin T → K))
    (hA : IsPolynomialFamily A)
    (hlambda : IsPolynomialFamily (fun p : (Fin (q₀+N) ⊕ Fin (finrank K X)) → K =>
      lambda (fun i => p (.inl i)) ((Module.finBasis K X).equivFun.symm (fun i => p (.inr i)))))
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (hcount : s₀+N+finrank K X<r+q*(a-k)+s) :
    ∃ Z : Fin s → Fin T → K,
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → Fin b → K))) K,
      (∃ Q : Fin q → Fin b → K,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
      ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
      ∀ (x : X) (t : Fin q₀ → K),
        (∀ i,eval t (f i).val=0) → eval t (ell 0).val=1 → ∀ u : Fin N → K,
        r≤finrank K (A (Fin.append t u)).range →
        lambda (Fin.append t u) x≠0 →
        finrank K (relationMap mu (lambda (Fin.append t u) x)).ker≤k →
        A (Fin.append t u) x=0 →
        ¬ ((∀ i v,covector (lambda (Fin.append t u) x) (mu (Q i) v+B i v)=0) ∧
          (∀ j,covector (lambda (Fin.append t u) x) (Z j)=0)) := by
  obtain ⟨P,hP,hgood⟩ := affine_layered_covectors_joint degrees f ell hempty
    A lambda hA hlambda mu B hcount
  obtain ⟨Z,D,hD,hDZ⟩ := principal_open_freeze_right P hP _ hgood
  exact ⟨Z,D,hD,hDZ⟩

end Froberg
