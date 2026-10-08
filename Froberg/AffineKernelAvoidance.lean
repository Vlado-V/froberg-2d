import Froberg.AffineKernelNormalized
import Froberg.IntrinsicFiniteOpen
import Quartic.HomogeneousSliceNormalization

/-! A joint scalar-and-cut open excluding every covector in one kernel
stratum. All full Grassmann charts and all bottom normalization charts are
intersected before any auxiliary cuts are chosen. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.BilinearCovectorCharts
open Quartic.BilinearCoefficientKernel Quartic.HomogeneousSliceNormalization
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {a b T T₀ H k q s s₀ nf r : ℕ}

theorem affine_kernel_stratum_joint
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (bottom : (Fin T → K) →ₗ[K] (Fin T₀ → K))
    (higher : (Fin T → K) →ₗ[K] (Fin H → K))
    (res : ((Fin T₀ → K) × (Fin H → K)) →ₗ[K] (Fin T → K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,covector ell (mu p v)=
      covector (bottom ell) (mu₀ p v)+covector (higher ell) (muH p v))
    (degrees : Fin nf → ℕ) (f : ∀ i,Forms K T₀ (degrees i))
    (cuts : Fin (s₀+1) → Forms K T₀ 1)
    (hempty : ∀ t : Fin T₀ → K,(∀ i,eval t (f i).val=0) →
      (∀ i,eval t (cuts i).val=0) → t=0)
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (hcount : s₀+a*k+(H+1)<r+q*(a-k)+s) :
    ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 →
      ∀ ell : Fin T → K,bottom ell≠0 →
        (∀ i,eval (bottom ell) (f i).val=0) →
        finrank K (relationMap mu ell).ker=k →
        r≤finrank K (BilinearImage.image muH (relationMap mu ell).ker) →
        KernelCovectorExcluded mu B y ell := by
  classical
  let C := Fin (s₀+1) × (Fin k ↪ Fin a)
  let Good : C → SharedCovectorPolynomial.Input K b T q s → Prop := fun c y =>
    ∀ ell : Fin T → K,ell≠0 →
      (∀ i,eval (bottom ell) (f i).val=0) → eval (bottom ell) (moveSlice cuts c.1 0).val=1 →
      ∀ u : Fin (graphParameterCount c.2) → K,
      Submodule.span K (Set.range (graphFromFin c.2 u))=(relationMap mu ell).ker →
      r≤finrank K (BilinearImage.image muH (relationMap mu ell).ker) →
      KernelCovectorExcluded mu B y ell
  have hchart (c : C) : ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 → Good c y := by
    apply affine_kernel_normalized_joint mu mu₀ muH bottom higher res hres hcompat
      degrees f (moveSlice cuts c.1) ?_ c.2 B hcount
    intro t hf ht
    apply hempty t hf
    intro i
    simpa only [moveSlice,Equiv.swap_apply_self] using ht (Equiv.swap 0 c.1 i)
  obtain ⟨D,hD,hgood⟩ := intrinsic_principal_common_open Good hchart
  refine ⟨D,hD,?_⟩
  intro y hy ell hbottom hf hk hr
  obtain ⟨i,hi⟩ : ∃ i,eval (bottom ell) (cuts i).val≠0 := by
    by_contra! he
    exact hbottom (hempty _ hf he)
  let c : K := (eval (bottom ell) (cuts i).val)⁻¹
  have hc : c≠0 := inv_ne_zero hi
  let ell' : Fin T → K := c • ell
  have hb : bottom ell'=c • bottom ell := map_smul bottom c ell
  have hker : (relationMap mu ell').ker=(relationMap mu ell).ker :=
    relationMap_kernel_smul mu c hc ell
  have hk' : finrank K (relationMap mu ell').ker=k := by rw [hker,hk]
  obtain ⟨j,u,hspan⟩ := exists_graphFromFin (relationMap mu ell').ker hk'
  have hell : ell≠0 := by
    intro he
    exact hbottom (by rw [he,map_zero])
  have hne : ell'≠0 := smul_ne_zero hc hell
  have hf' : ∀ l,eval (bottom ell') (f l).val=0 := by
    intro l
    rw [hb,eval_smul,hf l,mul_zero]
  have hs : eval (bottom ell') (moveSlice cuts i 0).val=1 := by
    rw [moveSlice_zero,hb,eval_smul,pow_one]
    exact inv_mul_cancel₀ hi
  have hr' : r≤finrank K (BilinearImage.image muH (relationMap mu ell').ker) := by
    rw [hker]
    exact hr
  have hex := hgood y hy (i,j) ell' hne hf' hs u hspan hr'
  intro hbad
  apply hex
  constructor
  · intro l v
    change covector (c • ell) _=0
    rw [covector_smul,LinearMap.smul_apply,hbad.1 l v,smul_zero]
  · intro l
    change covector (c • ell) _=0
    rw [covector_smul,LinearMap.smul_apply,hbad.2 l,smul_zero]

/-- Zero bottom cuts are allowed: then the homogeneous equations already
force the bottom covector to vanish. -/
theorem affine_kernel_stratum_joint_cuts
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (mu₀ : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T₀ → K))
    (muH : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin H → K))
    (bottom : (Fin T → K) →ₗ[K] (Fin T₀ → K))
    (higher : (Fin T → K) →ₗ[K] (Fin H → K))
    (res : ((Fin T₀ → K) × (Fin H → K)) →ₗ[K] (Fin T → K))
    (hres : ∀ ell,res (bottom ell,higher ell)=ell)
    (hcompat : ∀ ell p v,covector ell (mu p v)=
      covector (bottom ell) (mu₀ p v)+covector (higher ell) (muH p v))
    (degrees : Fin nf → ℕ) (f : ∀ i,Forms K T₀ (degrees i))
    (cuts : Fin s₀ → Forms K T₀ 1)
    (hempty : ∀ t : Fin T₀ → K,(∀ i,eval t (f i).val=0) →
      (∀ i,eval t (cuts i).val=0) → t=0)
    (B : Fin q → (Fin a → K) →ₗ[K] (Fin T → K))
    (hcount : s₀+a*k+H<r+q*(a-k)+s) :
    ∃ D : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ y : SharedCovectorPolynomial.Input K b T q s,eval ((Module.finBasis K _).equivFun y) D≠0) ∧
      ∀ y,eval ((Module.finBasis K _).equivFun y) D≠0 →
      ∀ ell : Fin T → K,bottom ell≠0 →
        (∀ i,eval (bottom ell) (f i).val=0) →
        finrank K (relationMap mu ell).ker=k →
        r≤finrank K (BilinearImage.image muH (relationMap mu ell).ker) →
        KernelCovectorExcluded mu B y ell := by
  cases s₀ with
  | zero =>
      refine ⟨1,⟨0,by simp only [map_one,ne_eq,one_ne_zero,not_false_eq_true]⟩,?_⟩
      intro y hy ell hb hf hk hr
      exact (hb (hempty (bottom ell) hf (fun i => Fin.elim0 i))).elim
  | succ n =>
      exact affine_kernel_stratum_joint mu mu₀ muH bottom higher res hres hcompat
        degrees f cuts hempty B (by omega)

end Froberg
