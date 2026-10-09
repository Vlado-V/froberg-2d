module

public import Froberg.AffinePolynomialSubstitution
public import Froberg.PolynomialLinearAvoidance

@[expose] public section

/-! A nonempty homogeneous-parameter open can be normalized to an affine
parameter open. The last coordinate is fixed at one only after selecting a
nonzero last coordinate; polynomial nonvanishing is retained explicitly. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open MvPolynomial Quartic
variable {K : Type*} [Field K] [Infinite K] {n : ℕ}

/-- Put a vector in the first coordinates and zero in the last coordinate. -/
def affineVectorLinear : (Fin n → K) →ₗ[K] (Fin (n+1) → K) where
  toFun x := Fin.snoc x 0
  map_add' x y := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Normalization of a principal open, for any condition invariant under
nonzero scalar multiplication of the full parameter vector. -/
theorem principal_open_affine_normalization
    (D : MvPolynomial (Fin (n+1)) K) (hD : ∃ y,eval y D≠0)
    (Good : (Fin (n+1) → K) → Prop)
    (hgood : ∀ y,eval y D≠0 → Good y)
    (hscale : ∀ (c : K),c≠0 → ∀ y,Good (c • y) → Good y) :
    ∃ P : MvPolynomial (Fin n) K,
      (∃ x,eval x P≠0) ∧ ∀ x,eval x P≠0 → Good (Fin.snoc x 1) := by
  classical
  let Ds : Fin 2 → MvPolynomial (Fin (n+1)) K := ![D,X (Fin.last n)]
  have hDs (i : Fin 2) : Ds i≠0 := by
    fin_cases i
    · obtain ⟨y,hy⟩ := hD
      intro hz
      have hz' : D=0 := hz
      exact hy (by rw [hz',map_zero])
    · simp [Ds]
  obtain ⟨y,hy⟩ := nonempty_principal_intersection Ds hDs
  let c := y (Fin.last n)
  have hc : c≠0 := by simpa [Ds,c] using hy 1
  let F := c • (affineVectorLinear (K := K) (n := n))
  let offset : Fin (n+1) → K := Fin.snoc 0 c
  have hF (x : Fin n → K) : F x+offset=c • Fin.snoc x 1 := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [F,offset,affineVectorLinear]
  let x₀ : Fin n → K := fun i => c⁻¹*y i.castSucc
  have hnormalize : c • Fin.snoc x₀ 1=y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [c]
    · simp [x₀,mul_inv_cancel_left₀ hc]
  refine ⟨substituteAffine F offset D,⟨x₀,?_⟩,?_⟩
  · rw [eval_substituteAffine,hF,hnormalize]
    exact hy 0
  · intro x hx
    rw [eval_substituteAffine,hF] at hx
    exact hscale c hc _ (hgood _ hx)

end Froberg
