import Froberg.IntrinsicQuotientSlices
import Froberg.PositiveIntrinsicKernelAvoidance
import Froberg.AffineKernelBudget

/-! The layered growth estimates and their exact finite budget yield
closed kernel slices on the actual quotient, on one common scalar open. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic BilinearScalarFamily QuotientCovectorKernel
variable {K P V V₀ W W₀ H : Type} [Field K] [Infinite K] [IsAlgClosed K]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W₀] [Module K W₀] [FiniteDimensional K W₀]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable {q M : ℕ}

theorem intrinsic_layered_quotient_slices_positive
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] V₀ →ₗ[K] W₀)
    (mu₀ : P →ₗ[K] V →ₗ[K] W₀) (muH : P →ₗ[K] V →ₗ[K] H)
    (bottom : (W →ₗ[K] K) →ₗ[K] (W₀ →ₗ[K] K))
    (higher : (W →ₗ[K] K) →ₗ[K] (H →ₗ[K] K))
    (res : ((W₀ →ₗ[K] K) × (H →ₗ[K] K)) →ₗ[K] (W →ₗ[K] K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,ell (mu p v)=(bottom ell) (mu₀ p v)+(higher ell) (muH p v))
    (s₀ : ℕ → ℕ) (hs₀ : HasClosedKernelSlices nu s₀)
    (hmono : ∀ ell : W →ₗ[K] K,bottom ell≠0 →
      finrank K (relation nu (bottom ell)).ker ≤ finrank K (relation mu ell).ker)
    (hgrowth : ∀ ell : W →ₗ[K] K,bottom ell≠0 →
      M*(finrank K (relation mu ell).ker-finrank K (relation nu (bottom ell)).ker) ≤
        finrank K (BilinearImage.image muH (relation mu ell).ker))
    (B : Fin q → V →ₗ[K] W) (A : (Fin q → P) → Submodule K W)
    (hA : ∀ Q i v,mu (Q i) v+B i v∈A Q) (slices : ℕ → ℕ)
    (E : MvPolynomial (Fin (finrank K (Fin q → P))) K)
    (hE : ∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) E≠0)
    (hdim : ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
      finrank K (W ⧸ A Q) ≤ slices 0)
    (hbottom : ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
      ∀ ell : W →ₗ[K] K,A Q ≤ ell.ker → bottom ell=0 → ell=0)
    (hcount : ∀ r : Fin (finrank K V+1),0<r.val →
      ∀ k : Fin (finrank K V+1),∀ k₀ : Fin (finrank K V₀+1),
      r.val ≤ k.val → k₀.val ≤ k.val → 0<s₀ k₀.val →
      s₀ k₀.val+finrank K V*k.val+finrank K H<
        M*(k.val-k₀.val)+q*(finrank K V-k.val)+slices r.val) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → P))) K,
      (∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
      ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
        eval ((Module.finBasis K _).equivFun Q) E≠0 ∧
        HasClosedKernelSlices (targetPostcompose mu (A Q).mkQ) slices := by
  apply kernel_avoidance_quotient_slices mu B bottom A hA slices E hE hdim hbottom
  intro r hr
  exact intrinsic_kernel_profiles_avoid_positive mu nu mu₀ muH bottom higher res hres hcompat
    s₀ hs₀ hmono hgrowth B (hcount r hr)

theorem intrinsic_uniform_quotient_slices_positive
    (mu : P →ₗ[K] V →ₗ[K] W) (nu : P →ₗ[K] V₀ →ₗ[K] W₀)
    (mu₀ : P →ₗ[K] V →ₗ[K] W₀) (muH : P →ₗ[K] V →ₗ[K] H)
    (bottom : (W →ₗ[K] K) →ₗ[K] (W₀ →ₗ[K] K))
    (higher : (W →ₗ[K] K) →ₗ[K] (H →ₗ[K] K))
    (res : ((W₀ →ₗ[K] K) × (H →ₗ[K] K)) →ₗ[K] (W →ₗ[K] K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,ell (mu p v)=(bottom ell) (mu₀ p v)+(higher ell) (muH p v))
    (s₀ : ℕ → ℕ) (hs₀ : HasClosedKernelSlices nu s₀)
    (hmono : ∀ ell : W →ₗ[K] K,bottom ell≠0 →
      finrank K (relation nu (bottom ell)).ker ≤ finrank K (relation mu ell).ker)
    (hgrowth : ∀ ell : W →ₗ[K] K,bottom ell≠0 →
      M*(finrank K (relation mu ell).ker-finrank K (relation nu (bottom ell)).ker) ≤
        finrank K (BilinearImage.image muH (relation mu ell).ker))
    (B : Fin q → V →ₗ[K] W) (A : (Fin q → P) → Submodule K W)
    (hA : ∀ Q i v,mu (Q i) v+B i v∈A Q) (slices : ℕ → ℕ)
    (E : MvPolynomial (Fin (finrank K (Fin q → P))) K)
    (hE : ∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) E≠0)
    (hdim : ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
      finrank K (W ⧸ A Q) ≤ slices 0)
    (hbottom : ∀ Q,eval ((Module.finBasis K _).equivFun Q) E≠0 →
      ∀ ell : W →ₗ[K] K,A Q ≤ ell.ker → bottom ell=0 → ell=0)
    (C L j H₀ : ℕ) (loss : ℕ → ℕ)
    (hbase : ∀ k₀ : Fin (finrank K V₀+1),0<s₀ k₀.val →
      s₀ k₀.val+C*k₀.val ≤ finrank K W₀)
    (hambient : finrank K W₀+finrank K H ≤ j+q*finrank K V+H₀)
    (hslices : ∀ r : Fin (finrank K V+1),0<r.val → j ≤ slices r.val+loss r.val)
    (hC : L ≤ C) (hM : L ≤ M)
    (hloss : ∀ r : Fin (finrank K V+1),0<r.val → loss r.val ≤ L*r.val/2)
    (hsmall : 2*(H₀+finrank K V+q)+1 ≤ L) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → P))) K,
      (∃ Q : Fin q → P,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
      ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
        eval ((Module.finBasis K _).equivFun Q) E≠0 ∧
        HasClosedKernelSlices (targetPostcompose mu (A Q).mkQ) slices := by
  apply intrinsic_layered_quotient_slices_positive mu nu mu₀ muH bottom higher res hres hcompat
    s₀ hs₀ hmono hgrowth B A hA slices E hE hdim hbottom
  intro r hr k k₀ ht hkk hs
  have hloss' : loss r.val≤L*k.val/2 := (hloss r hr).trans
    (Nat.div_le_div_right (Nat.mul_le_mul_left L ht))
  exact layered_covector_equation_budget (by omega) hkk (hbase k₀ hs) hambient
    (le_refl _) (hslices r hr)
    (layered_covector_gain (hr.trans_le ht) hkk hC hM hloss' hsmall)

end Froberg
