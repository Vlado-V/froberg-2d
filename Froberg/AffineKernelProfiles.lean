module

public import Froberg.AffineKernelAvoidance
public import Froberg.FreezeParameters

@[expose] public section

/-! Simultaneous actual kernel profiles. The auxiliary cuts remain variable
through both the chart and profile intersections and are fixed only once. -/
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.BilinearCovectorCharts
open Quartic.BilinearCoefficientKernel
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {a a₀ b T T₀ H q s threshold M : ℕ}

section Model
variable
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (nu : (Fin b → K) →ₗ[K] (Fin a₀ → K) →ₗ[K] (Fin T₀ → K))
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (bottom : (Fin T → K) →ₗ[K] (Fin T₀ → K))
    (higher : (Fin T → K) →ₗ[K] (Fin H → K))
    (res : ((Fin T₀ → K) × (Fin H → K)) →ₗ[K] (Fin T → K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,covector ell (mu p v)=
      covector (bottom ell) (mu₀ p v)+covector (higher ell) (muH p v))
    (s₀ nf : Fin (a₀+1) → ℕ)
    (degrees : (k₀ : Fin (a₀+1)) → Fin (nf k₀) → ℕ)
    (f : (k₀ : Fin (a₀+1)) → (i : Fin (nf k₀)) → Forms K T₀ (degrees k₀ i))
    (cuts : (k₀ : Fin (a₀+1)) → Fin (s₀ k₀) → Forms K T₀ 1)
    (hempty : ∀ k₀ (t : Fin T₀ → K),(∀ i,eval t (f k₀ i).val=0) →
      (∀ i,eval t (cuts k₀ i).val=0) → t=0)
    (hpresentation : ∀ k₀ (t : Fin T₀ → K),
      finrank K (relationMap nu t).ker=k₀.val → ∀ i,eval t (f k₀ i).val=0)
    (hmono : ∀ ell : Fin T → K,bottom ell≠0 →
      finrank K (relationMap nu (bottom ell)).ker≤finrank K (relationMap mu ell).ker)
    (hgrowth : ∀ ell : Fin T → K,bottom ell≠0 →
      M*(finrank K (relationMap mu ell).ker-finrank K (relationMap nu (bottom ell)).ker)≤
        finrank K (BilinearImage.image muH (relationMap mu ell).ker))
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (hcount : ∀ k : Fin (a+1),∀ k₀ : Fin (a₀+1),threshold≤k.val → k₀.val≤k.val →
      s₀ k₀+a*k.val+H<M*(k.val-k₀.val)+q*(a-k.val)+s)

include nu mu₀ muH higher res hres hcompat s₀ nf degrees f cuts hempty hpresentation hmono hgrowth hcount

/-- A single joint principal open works for every full and bottom kernel
profile. There is no choice of cuts depending on a profile or covector. -/
theorem affine_kernel_profiles_joint :
    ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 →
      ∀ ell : Fin T → K,bottom ell≠0 → threshold≤finrank K (relationMap mu ell).ker →
        KernelCovectorExcluded mu B y ell := by
  classical
  let C := {p : Fin (a+1) × Fin (a₀+1) // threshold≤p.1.val ∧ p.2.val≤p.1.val}
  let Good : C → SharedCovectorPolynomial.Input K b T q s → Prop := fun c y =>
    ∀ ell : Fin T → K,bottom ell≠0 →
      (∀ i,eval (bottom ell) (f c.val.2 i).val=0) →
      finrank K (relationMap mu ell).ker=c.val.1.val →
      M*(c.val.1.val-c.val.2.val)≤finrank K (BilinearImage.image muH (relationMap mu ell).ker) →
      KernelCovectorExcluded mu B y ell
  have hc (c : C) : ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 → Good c y :=
    affine_kernel_stratum_joint_cuts mu mu₀ muH bottom higher res hres hcompat
      (degrees c.val.2) (f c.val.2) (cuts c.val.2) (hempty c.val.2) B
      (hcount c.val.1 c.val.2 c.property.1 c.property.2)
  obtain ⟨D,hD,hgood⟩ := intrinsic_principal_common_open Good hc
  refine ⟨D,hD,?_⟩
  intro y hy ell hb ht
  have hk : finrank K (relationMap mu ell).ker≤a := by
    simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using (Submodule.finrank_le (relationMap mu ell).ker)
  have hk₀ : finrank K (relationMap nu (bottom ell)).ker≤a₀ := by
    simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using (Submodule.finrank_le (relationMap nu (bottom ell)).ker)
  let k : Fin (a+1) := ⟨finrank K (relationMap mu ell).ker,by omega⟩
  let k₀ : Fin (a₀+1) := ⟨finrank K (relationMap nu (bottom ell)).ker,by omega⟩
  let c : C := ⟨(k,k₀),ht,hmono ell hb⟩
  exact hgood y hy c ell hb (hpresentation k₀ (bottom ell) rfl) rfl (hgrowth ell hb)

/-- Freeze the target cuts only after the full finite profile intersection. -/
theorem affine_kernel_profiles_avoid :
    ∃ Z : Fin s → Fin T → K,
    ∃ D : MvPolynomial (Fin (finrank K (Fin q → Fin b → K))) K,
      (∃ Q : Fin q → Fin b → K,eval ((Module.finBasis K _).equivFun Q) D≠0) ∧
      ∀ Q,eval ((Module.finBasis K _).equivFun Q) D≠0 →
      ∀ ell : Fin T → K,bottom ell≠0 → threshold≤finrank K (relationMap mu ell).ker →
        KernelCovectorExcluded mu B (Q,Z) ell := by
  obtain ⟨P,hP,hgood⟩ := affine_kernel_profiles_joint mu nu mu₀ muH bottom higher res hres hcompat
    s₀ nf degrees f cuts hempty hpresentation hmono hgrowth B hcount
  exact principal_open_freeze_right P hP _ hgood

end Model
end Froberg
