import Quartic.RationalKernelExtension

/-!
# Generic avoidance of successive dependent kernel constraints

The second matrix depends on both the original parameter and the first
kernel vector. Its rank contribution is justified after reconstructing that
vector, using rational substitution and clearing denominators. Thus the
codimensions add without assuming independent or fixed constraint groups.
-/
noncomputable section
namespace Quartic.SuccessiveKernelAvoidance
open Matrix MvPolynomial RationalImageAvoidance KernelPolynomialCharts
variable {K I : Type*} [Field K] [Infinite K] [Fintype I] {a b n l r s : ℕ}

/-- A nonempty principal open avoids two successive kernel conditions when
the sum of their actual rank bounds exceeds the original parameter count. -/
theorem principal_open_avoids_two_stage_kernels
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : Fintype.card I < r+s) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin l) K,
      (∃ z : Fin n ⊕ Fin l → K, eval z P ≠ 0) ∧
      ∀ z, eval z P ≠ 0 → ∀ t : I → K,
        r ≤ (evaluated A t).rank →
        s ≤ (evaluated B (Sum.elim t (fun i => z (Sum.inl i)))).rank →
        evaluated A t *ᵥ (fun i => z (Sum.inl i)) ≠ 0 ∨
        evaluated B (Sum.elim t (fun i => z (Sum.inl i))) *ᵥ (fun j => z (Sum.inr j)) ≠ 0 := by
  classical
  let C₁ := (Fin r ↪ Fin a) × (Fin r ↪ Fin n)
  let C₂ := (Fin s ↪ Fin b) × (Fin s ↪ Fin l)
  let F₀ : I → MvPolynomial I K := fun i => X i
  let G₀ : MvPolynomial I K := 1
  let Param₁ (c : C₁) := RationalKernelExtension.Parameters I c.2
  let F₁ (c : C₁) := RationalKernelExtension.numerator F₀ G₀ A c.1 c.2
  let G₁ (c : C₁) := RationalKernelExtension.denominator F₀ G₀ A c.1 c.2
  let Param (c : C₁ × C₂) := RationalKernelExtension.Parameters (Param₁ c.1) c.2.2
  let N (c : C₁ × C₂) := RationalKernelExtension.numerator (F₁ c.1) (G₁ c.1) B c.2.1 c.2.2
  let D (c : C₁ × C₂) := RationalKernelExtension.denominator (F₁ c.1) (G₁ c.1) B c.2.1 c.2.2
  let F (c : C₁ × C₂) : Fin n ⊕ Fin l → MvPolynomial (Param c) K :=
    Sum.elim (fun i => N c (Sum.inl (Sum.inr i))) (fun j => N c (Sum.inr j))
  have hdim (c : C₁ × C₂) : Fintype.card (Param c) < Fintype.card (Fin n ⊕ Fin l) := by
    have hrn : r ≤ n := by simpa using Fintype.card_le_of_injective c.1.2 c.1.2.injective
    have hsl : s ≤ l := by simpa using Fintype.card_le_of_injective c.2.2 c.2.2.injective
    change Fintype.card (RationalKernelExtension.Parameters (Param₁ c.1) c.2.2) < _
    rw [RationalKernelExtension.parameter_count]
    change Fintype.card (RationalKernelExtension.Parameters I c.1.2) + (l-s) < _
    rw [RationalKernelExtension.parameter_count,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin]
    omega
  obtain ⟨P,hP,havoid⟩ := principal_open_avoids_finite_union Param F D hdim
  refine ⟨P,hP,?_⟩
  intro z hz t hr hs
  by_contra! hbad
  have hbase : rationalMap F₀ G₀ t = t := by ext i; simp [rationalMap,F₀,G₀]
  have hG₀ : eval t G₀ ≠ 0 := by simp [G₀]
  obtain ⟨u₁,v₁,p₁,_,hp₁,he₁⟩ := RationalKernelExtension.cover F₀ G₀ A t hG₀
    (by simpa only [hbase] using hr) (fun i => z (Sum.inl i)) (by simpa only [hbase] using hbad.1)
  let c₁ : C₁ := (u₁,v₁)
  have he₁' : rationalMap (F₁ c₁) (G₁ c₁) p₁ = Sum.elim t (fun i => z (Sum.inl i)) := by
    simpa only [hbase] using he₁
  obtain ⟨u₂,v₂,p₂,_,hp₂,he₂⟩ := RationalKernelExtension.cover (F₁ c₁) (G₁ c₁) B p₁ hp₁
    (by simpa only [he₁'] using hs) (fun j => z (Sum.inr j)) (by simpa only [he₁'] using hbad.2)
  let c : C₁ × C₂ := (c₁,(u₂,v₂))
  have he : rationalMap (F c) (D c) p₂ = z := by
    funext k
    cases k with
    | inl i =>
      have h := congrFun he₂ (Sum.inl (Sum.inr i))
      simpa only [he₁',rationalMap,F,N,D,c,Sum.elim_inl,Sum.elim_inr] using h
    | inr j =>
      have h := congrFun he₂ (Sum.inr j)
      simpa only [rationalMap,F,N,D,c,Sum.elim_inr] using h
  exact havoid z hz c p₂ hp₂ he.symm

end Quartic.SuccessiveKernelAvoidance
