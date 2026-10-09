module

public import Froberg.GenericDimensions

@[expose] public section

/-! Combining a nonempty joint open with nonempty opens chosen in each fiber.
No uniform polynomial certificate for the fiber property is assumed. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K I J : Type*} [Field K] [Infinite K]

def polynomialFixRight (y : J → K) : MvPolynomial (I ⊕ J) K →ₐ[K] MvPolynomial I K :=
  aeval (Sum.elim X (fun j => C (y j)))

def polynomialFixLeft (x : I → K) : MvPolynomial (I ⊕ J) K →ₐ[K] MvPolynomial J K :=
  aeval (Sum.elim (fun i => C (x i)) X)

lemma eval_polynomialFixRight (x : I → K) (y : J → K) (P : MvPolynomial (I ⊕ J) K) :
    eval x (polynomialFixRight y P)=eval (Sum.elim x y) P := by
  have hh : (aeval x).comp (polynomialFixRight y)=aeval (Sum.elim x y) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [polynomialFixRight]
  exact congrArg (fun f : MvPolynomial (I ⊕ J) K →ₐ[K] K => f P) hh

lemma eval_polynomialFixLeft (x : I → K) (y : J → K) (P : MvPolynomial (I ⊕ J) K) :
    eval y (polynomialFixLeft x P)=eval (Sum.elim x y) P := by
  have hh : (aeval y).comp (polynomialFixLeft x)=aeval (Sum.elim x y) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [polynomialFixLeft]
  exact congrArg (fun f : MvPolynomial (I ⊕ J) K →ₐ[K] K => f P) hh

theorem fiberwise_principal_meets_joint_open
    (D : MvPolynomial I K) (hD : ∃ x,eval x D ≠ 0)
    (Φ : (I → K) → (J → K) → Prop)
    (hΦ : ∀ x,eval x D ≠ 0 → ∃ Q : MvPolynomial J K,
      (∃ y,eval y Q ≠ 0) ∧ ∀ y,eval y Q ≠ 0 → Φ x y)
    (P : MvPolynomial (I ⊕ J) K) (hP : ∃ z,eval z P ≠ 0) :
    ∃ x y,eval x D ≠ 0 ∧ Φ x y ∧ eval (Sum.elim x y) P ≠ 0 := by
  obtain ⟨z,hz⟩ := hP
  let x₀ : I → K := fun i => z (.inl i)
  let y₀ : J → K := fun j => z (.inr j)
  have hz' : eval (Sum.elim x₀ y₀) P ≠ 0 := by
    have he : Sum.elim x₀ y₀=z := by funext i; cases i <;> rfl
    rwa [he]
  have hR : ∃ x,eval x (polynomialFixRight y₀ P) ≠ 0 :=
    ⟨x₀,by simpa only [eval_polynomialFixRight] using hz'⟩
  obtain ⟨x,hxD,hxR⟩ := principal_opens_intersect hD hR
  obtain ⟨Q,hQ,hprop⟩ := hΦ x hxD
  have hL : ∃ y,eval y (polynomialFixLeft x P) ≠ 0 := by
    refine ⟨y₀,?_⟩
    simpa only [eval_polynomialFixLeft,eval_polynomialFixRight] using hxR
  obtain ⟨y,hyQ,hyL⟩ := principal_opens_intersect hQ hL
  exact ⟨x,y,hxD,hprop y hyQ,by simpa only [eval_polynomialFixLeft] using hyL⟩

theorem fiberwise_principal_meets_joint_open_with_extra {L : Type*}
    (D : MvPolynomial I K) (hD : ∃ x,eval x D ≠ 0)
    (Φ : (I → K) → (J → K) → Prop)
    (hΦ : ∀ x,eval x D ≠ 0 → ∃ Q : MvPolynomial J K,
      (∃ y,eval y Q ≠ 0) ∧ ∀ y,eval y Q ≠ 0 → Φ x y)
    (P : MvPolynomial (I ⊕ (J ⊕ L)) K) (hP : ∃ z,eval z P ≠ 0) :
    ∃ x y z,eval x D ≠ 0 ∧ Φ x y ∧ eval (Sum.elim x (Sum.elim y z)) P ≠ 0 := by
  have hΦ' : ∀ x,eval x D ≠ 0 → ∃ Q : MvPolynomial (J ⊕ L) K,
      (∃ y,eval y Q ≠ 0) ∧ ∀ y,eval y Q ≠ 0 → Φ x (fun j => y (.inl j)) := by
    intro x hx
    obtain ⟨Q,⟨y,hy⟩,hgood⟩ := hΦ x hx
    refine ⟨rename Sum.inl Q,⟨Sum.elim y 0,?_⟩,?_⟩
    · simpa only [eval_rename,Function.comp_def,Sum.elim_inl] using hy
    · intro z hz
      apply hgood
      simpa only [eval_rename,Function.comp_def] using hz
  obtain ⟨x,y,hx,hxy,hyP⟩ := fiberwise_principal_meets_joint_open D hD _ hΦ' P hP
  refine ⟨x,(fun j => y (.inl j)),(fun l => y (.inr l)),hx,hxy,?_⟩
  have he : Sum.elim (fun j => y (.inl j)) (fun l => y (.inr l))=y := by
    funext t
    cases t <;> rfl
  rwa [he]

end Froberg
