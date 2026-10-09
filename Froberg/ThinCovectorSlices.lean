module

public import Froberg.ThinShadowBudget
public import Froberg.AffinePolynomialSubstitution
public import Quartic.ExpansionClosedSlices

@[expose] public section

/-! One actual scalar tuple open and fixed linear slices for every closed
kernel threshold in the thin range. -/
noncomputable section
namespace Froberg.BilinearCovectorStrata
open Module MvPolynomial Quartic
open BilinearCovectorCharts BilinearCoefficientKernel PolynomialBilinearCoordinates
variable {K : Type*} [Field K] [Infinite K] {a b T q j : ℕ}

theorem principal_open_fixed_threshold_slices
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (slices : ℕ → ℕ) (hmono : Antitone slices)
    (hcount : ∀ ell : Fin T → K,ell ≠ 0 →
      let r := finrank K (LinearMap.ker (relationMap mu ell))
      let E := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
      (r*(a-r) : ℕ)+(T : ℤ)-E-1 < (q*(a-r)+slices r : ℕ)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      ∃ cuts : (r : Fin (a+1)) → Fin (slices r.val) → Fin T → K,
      (∃ Q,eval Q P ≠ 0) ∧ ∀ Q,eval Q P ≠ 0 →
        ∀ r : Fin (a+1),∀ ell : Fin T → K,
          r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
          ((∀ i v,covector ell (mu (fun k => Q (i,k)) v)=0) ∧
            (∀ t,covector ell (cuts r t)=0)) → ell=0 := by
  classical
  obtain ⟨P,⟨x,hx⟩,hgood⟩ := ExpansionClosedSlices.principal_open_all_thresholds
    mu slices hmono hcount
  let V := ExpansionClosedSlices.Input K a b T q slices
  let inc : ((Fin q × Fin b) → K) →ₗ[K] V :=
    (LinearMap.pi (fun i => LinearMap.pi (fun k => LinearMap.proj (i,k)))).prod 0
  let F := (coordinates K V).toLinearMap.comp inc
  let c := coordinates K V (0,x.2)
  have heval (Q : (Fin q × Fin b) → K) :
      eval Q (substituteAffine F c P)=
        eval (coordinates K V (fun i k => Q (i,k),x.2)) P := by
    rw [eval_substituteAffine]
    congr 2
    change coordinates K V (inc Q)+coordinates K V (0,x.2)=_
    rw [← map_add]
    congr 1
    apply Prod.ext
    · change (fun i k => Q (i,k))+(0 : Fin q → Fin b → K)=_
      exact add_zero _
    · change 0+x.2=x.2
      exact zero_add _
  refine ⟨substituteAffine F c P,x.2,⟨fun ik => x.1 ik.1 ik.2,?_⟩,?_⟩
  · simpa only [heval] using hx
  · intro Q hQ r ell hr hann
    exact hgood (fun i k => Q (i,k),x.2) ((heval Q).symm ▸ hQ) r ell hr hann

theorem principal_open_thin_slices
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (ha : 0 < a) (hT : T=q*a+j) (G C : ℝ) (hC : 0 ≤ C)
    (hG₁ : (a : ℝ)+C ≤ G) (hG₂ : (a : ℝ)+(j : ℝ)/a ≤ G)
    (hgrowth : ∀ U : Submodule K (Fin a → K),
      ((T : ℝ)/a)*finrank K U+G*(min (finrank K U) (a-finrank K U) : ℕ) ≤
        finrank K (BilinearImage.image mu U)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      ∃ cuts : (r : Fin (a+1)) → Fin (thinSlices j C r.val) → Fin T → K,
      (∃ Q,eval Q P ≠ 0) ∧ ∀ Q,eval Q P ≠ 0 →
        ∀ r : Fin (a+1),∀ ell : Fin T → K,
          r.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
          ((∀ i v,covector ell (mu (fun k => Q (i,k)) v)=0) ∧
            (∀ t,covector ell (cuts r t)=0)) → ell=0 := by
  apply principal_open_fixed_threshold_slices mu (thinSlices j C) (thinSlices_antitone j hC)
  intro ell hell
  apply thin_covector_budget ha (by simpa using (LinearMap.ker (relationMap mu ell)).finrank_le)
    hT G C hC hG₁ hG₂
  exact hgrowth _

end Froberg.BilinearCovectorStrata
