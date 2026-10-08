import Froberg.PreparedBiformCoordinates
import Froberg.ConstrainedCrossPair
import Froberg.BalancedScalarCoordinates

/-! Cross products remain independent with unequal output blocks. This
supplies the two-fifths / three-fifths split of Appendix E. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.UnequalBlocks
open MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {a b v : ℕ}

abbrev Variables (a b v : ℕ) := (Fin a ⊕ Fin b) ⊕ (Fin v × Bool)

def leftVar : Fin a ⊕ Fin v → Variables a b v
  | .inl x => .inl (.inl x)
  | .inr y => .inr (y,true)

def rightVar : Fin b ⊕ Fin v → Variables a b v
  | .inl x => .inl (.inr x)
  | .inr y => .inr (y,false)

def regroup : ((Fin a ⊕ Fin v) ⊕ (Fin b ⊕ Fin v)) ≃ Variables a b v where
  toFun := Sum.elim leftVar rightVar
  invFun := fun z => match z with
    | .inl (.inl x) => .inl (.inl x)
    | .inl (.inr x) => .inr (.inl x)
    | .inr (y,c) => if c then .inl (.inr y) else .inr (.inr y)
  left_inv := by rintro ((x|y)|(x|y)) <;> rfl
  right_inv := by
    rintro ((x|x)|⟨y,c⟩)
    · rfl
    · rfl
    · cases c <;> rfl

def finalEquiv : Variables a b v ≃ (Fin (a+b) ⊕ Fin (v+v)) :=
  finSumFinEquiv.sumCongr (pairedScalarEquiv v)

def leftFinal : Fin a ⊕ Fin v → Fin (a+b) ⊕ Fin (v+v) :=
  finalEquiv ∘ leftVar

def rightFinal : Fin b ⊕ Fin v → Fin (a+b) ⊕ Fin (v+v) :=
  finalEquiv ∘ rightVar

theorem leftFinal_eq : (leftFinal (a := a) (b := b) (v := v)) =
    Sum.map (Fin.castAdd b) (fun y => pairedScalarEquiv v (y,true)) := by
  funext z
  cases z <;> rfl

theorem rightFinal_eq : (rightFinal (a := a) (b := b) (v := v)) =
    Sum.map (Fin.natAdd a) (fun y => pairedScalarEquiv v (y,false)) := by
  funext z
  cases z <;> rfl

theorem cross_independent {r t : ℕ}
    (f : Fin r → MvPolynomial (Fin a ⊕ Fin v) K)
    (g : Fin t → MvPolynomial (Fin b ⊕ Fin v) K)
    (hf : LinearIndependent K f) (hg : LinearIndependent K g) :
    LinearIndependent K (fun p : Fin r × Fin t =>
      rename leftFinal (f p.1)*rename rightFinal (g p.2)) := by
  let E := (regroup (a := a) (b := b) (v := v)).trans finalEquiv
  have h := (linearIndependent_cross_products_disjoint f g hf hg).map'
    (rename E).toLinearMap (LinearMap.ker_eq_bot.mpr (rename_injective _ E.injective))
  convert h using 1
  funext p
  simp only [Function.comp_apply,AlgHom.toLinearMap_apply,map_mul,rename_rename]
  rfl

end Froberg.UnequalBlocks

namespace Froberg
open Module MvPolynomial UnequalBlocks
variable {K : Type} [Field K] [Infinite K]

/-- Unequal output blocks and balanced scalar blocks give the full tensor
cross capacity, with a single scalar profile for every product. -/
theorem exists_unequal_constrained_cross_pair
    {X₁ X₂ : Type*} [AddCommGroup X₁] [Module K X₁] [Module.Finite K X₁]
    [AddCommGroup X₂] [Module K X₂] [Module.Finite K X₂]
    {a b v j l s t r u : ℕ} (ha : 0<a) (hb : 0<b) (hv : 0<v)
    (T₁ : Poly K (a+b) →ₗ[K] X₁) (T₂ : Poly K (a+b) →ₗ[K] X₂)
    (hr : r≤((a+j-1).choose j-finrank K X₁)*(v+s-1).choose s)
    (hu : u≤((b+l-1).choose l-finrank K X₂)*(v+t-1).choose t) :
    ∃ (f : Fin r → MvPolynomial (Fin (a+b) ⊕ Fin (v+v)) K)
      (g : Fin u → MvPolynomial (Fin (a+b) ⊕ Fin (v+v)) K),
      (∀ i,f i∈biformImage (Forms K (a+b) j⊓T₁.ker) (Forms K (v+v) s)) ∧
      (∀ i,g i∈biformImage (Forms K (a+b) l⊓T₂.ker) (Forms K (v+v) t)) ∧
      (∀ i,(f i).IsWeightedHomogeneous
        (Sum.elim (fun _ : Fin (a+b) => 0) (ProductRows.halfWeight (balancedScalarHalf v))) s) ∧
      (∀ i,(g i).IsWeightedHomogeneous
        (Sum.elim (fun _ : Fin (a+b) => 0) (ProductRows.halfWeight (balancedScalarHalf v))) 0) ∧
      LinearIndependent K (fun p : Fin r × Fin u => f p.1*g p.2) := by
  let O₁ := Forms K a j⊓(T₁.comp (rename (Fin.castAdd b)).toLinearMap).ker
  let O₂ := Forms K b l⊓(T₂.comp (rename (Fin.natAdd a)).toLinearMap).ker
  letI : Module.Finite K O₁ := Submodule.finiteDimensional_of_le (show O₁≤Forms K a j from inf_le_left)
  letI : Module.Finite K O₂ := Submodule.finiteDimensional_of_le (show O₂≤Forms K b l from inf_le_left)
  have hdim₁ := finrank_intersection_kernel_lower_bound (Forms K a j)
    (T₁.comp (rename (Fin.castAdd b)).toLinearMap)
  have hdim₂ := finrank_intersection_kernel_lower_bound (Forms K b l)
    (T₂.comp (rename (Fin.natAdd a)).toLinearMap)
  rw [finrank_forms K a j ha] at hdim₁
  rw [finrank_forms K b l hb] at hdim₂
  obtain ⟨f,hf,hfi⟩ := exists_independent_sum_biforms O₁ (Forms K v s)
    (hr.trans (by rw [finrank_forms K v s hv]; exact Nat.mul_le_mul_right _ hdim₁))
  obtain ⟨g,hg,hgi⟩ := exists_independent_sum_biforms O₂ (Forms K v t)
    (hu.trans (by rw [finrank_forms K v t hv]; exact Nat.mul_le_mul_right _ hdim₂))
  refine ⟨fun i => rename leftFinal (f i),fun i => rename rightFinal (g i),?_,?_,?_,?_,
    UnequalBlocks.cross_independent f g hfi hgi⟩
  · intro i
    rw [leftFinal_eq]
    have hmem := biformImage_rename (Fin.castAdd b) (fun y : Fin v => pairedScalarEquiv v (y,true))
      O₁ (Forms K v s) ⟨f i,hf i,rfl⟩
    apply biformImage_mono ?_ ?_ hmem
    · rintro p ⟨q,hq,rfl⟩
      exact ⟨hq.1.rename_isHomogeneous,hq.2⟩
    · rintro p ⟨q,hq,rfl⟩
      exact hq.rename_isHomogeneous
  · intro i
    rw [rightFinal_eq]
    have hmem := biformImage_rename (Fin.natAdd a) (fun y : Fin v => pairedScalarEquiv v (y,false))
      O₂ (Forms K v t) ⟨g i,hg i,rfl⟩
    apply biformImage_mono ?_ ?_ hmem
    · rintro p ⟨q,hq,rfl⟩
      exact ⟨hq.1.rename_isHomogeneous,hq.2⟩
    · rintro p ⟨q,hq,rfl⟩
      exact hq.rename_isHomogeneous
  · intro i
    apply rename_weightedHomogeneous
      (⟨leftFinal,(finalEquiv (a := a) (b := b) (v := v)).injective.comp
        ((regroup (a := a) (b := b) (v := v)).injective.comp Sum.inl_injective)⟩ :
          (Fin a ⊕ Fin v) ↪ (Fin (a+b) ⊕ Fin (v+v)))
      FourBlocks.scalarWeight _ _ (biformImage_scalar_weight O₁ (Forms K v s) le_rfl (hf i))
    rintro (x|y)
    · rfl
    · exact pairedScalarEquiv_halfWeight v (y,true)
  · intro i
    apply rename_weightedHomogeneous
      (⟨rightFinal,(finalEquiv (a := a) (b := b) (v := v)).injective.comp
        ((regroup (a := a) (b := b) (v := v)).injective.comp Sum.inr_injective)⟩ :
          (Fin b ⊕ Fin v) ↪ (Fin (a+b) ⊕ Fin (v+v)))
      (fun _ => 0) _ _ (weightedHomogeneous_zero_weight (g i))
    rintro (x|y)
    · rfl
    · exact pairedScalarEquiv_halfWeight v (y,false)

end Froberg
