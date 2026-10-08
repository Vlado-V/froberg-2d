import Froberg.BiformOutputConstraint

/-! Cross-pair product witnesses with arbitrary finite-dimensional output
constraints, at the full half-variable tensor capacity. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]

variable {X : Type*} [AddCommGroup X] [Module K X]

def halfConstrainedSpace (w j : ℕ) (b : Bool)
    (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X) : Submodule K (Poly K w) :=
  Forms K w j ⊓ (T.comp (rename (fun x : Fin w => (x,b))).toLinearMap).ker

instance (w j : ℕ) (b : Bool) (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X) :
    Module.Finite K (halfConstrainedSpace w j b T) :=
  Submodule.finiteDimensional_of_le inf_le_left

theorem halfConstrainedSpace_dimension [Module.Finite K X] {w : ℕ} (hw : 0<w)
    (j : ℕ) (b : Bool) (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X) :
    (w+j-1).choose j - finrank K X ≤ finrank K (halfConstrainedSpace w j b T) := by
  have h := finrank_intersection_kernel_lower_bound (Forms K w j)
    (T.comp (rename (fun x : Fin w => (x,b))).toLinearMap)
  rwa [finrank_forms K w j hw] at h

theorem halfConstrainedSpace_output_kernel {w v j : ℕ} (b : Bool)
    (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (C : Submodule K (Poly K v)) :
    (biformImage (halfConstrainedSpace w j b T) C).map
      (rename (Sum.map (fun x : Fin w => (x,b)) (fun y : Fin v => (y,b)))).toLinearMap ≤
        (biformOutputMap (τ := Fin v × Bool) T).ker := by
  apply (biformImage_rename _ _ _ _).trans
  apply biformImage_le_output_kernel
  rintro f ⟨g,hg,rfl⟩
  exact hg.2

theorem biformImage_half_output_weight {w v j : ℕ} (b : Bool)
    (O : Submodule K (Poly K w)) (C : Submodule K (Poly K v)) (hO : O ≤ Forms K w j) :
    (biformImage O C).map
      (rename (Sum.map (fun x : Fin w => (x,b)) (fun y : Fin v => (y,b)))).toLinearMap ≤
        weightedHomogeneousSubmodule K
          (FourBlocks.outputWeight (A := Fin w × Bool) (B := Fin v × Bool)) j := by
  rintro f ⟨g,hg,rfl⟩
  apply rename_weightedHomogeneous
    (⟨Sum.map (fun x : Fin w => (x,b)) (fun y : Fin v => (y,b)),
      Sum.map_injective.mpr ⟨(fun _ _ h => congrArg Prod.fst h), (fun _ _ h => congrArg Prod.fst h)⟩⟩ :
      (Fin w ⊕ Fin v) ↪ ((Fin w × Bool) ⊕ (Fin v × Bool)))
    FourBlocks.outputWeight FourBlocks.outputWeight _ (biformImage_output_weight O C hO hg)
  rintro (x|y) <;> rfl

/-- Arbitrary finite output constraints cost at most their target dimension
in each half-space; all cross products remain independent. -/
theorem exists_constrained_fourBlock_cross_pair
    {X₁ X₂ : Type*} [AddCommGroup X₁] [Module K X₁] [Module.Finite K X₁]
    [AddCommGroup X₂] [Module K X₂] [Module.Finite K X₂]
    {w v j l s t a b : ℕ} (hw : 0<w) (hv : 0<v)
    (T₁ : MvPolynomial (Fin w × Bool) K →ₗ[K] X₁)
    (T₂ : MvPolynomial (Fin w × Bool) K →ₗ[K] X₂)
    (ha : a ≤ ((w+j-1).choose j - finrank K X₁) * (v+s-1).choose s)
    (hb : b ≤ ((w+l-1).choose l - finrank K X₂) * (v+t-1).choose t) :
    ∃ (f : Fin a → MvPolynomial (FourBlocks.Variables (Fin w) (Fin v)) K)
      (g : Fin b → MvPolynomial (FourBlocks.Variables (Fin w) (Fin v)) K),
      (∀ i, (f i).IsHomogeneous (j+s) ∧
        (f i).IsWeightedHomogeneous FourBlocks.xHalfWeight j ∧
        (f i).IsWeightedHomogeneous FourBlocks.yHalfWeight s ∧ biformOutputMap T₁ (f i)=0) ∧
      (∀ i, (g i).IsHomogeneous (l+t) ∧
        (g i).IsWeightedHomogeneous FourBlocks.xHalfWeight 0 ∧
        (g i).IsWeightedHomogeneous FourBlocks.yHalfWeight 0 ∧ biformOutputMap T₂ (g i)=0) ∧
      LinearIndependent K (fun p : Fin a × Fin b => f p.1 * g p.2) ∧
      (∀ i, (f i).IsWeightedHomogeneous (FourBlocks.outputWeight (A := Fin w × Bool) (B := Fin v × Bool)) j) ∧
      (∀ i, (g i).IsWeightedHomogeneous (FourBlocks.outputWeight (A := Fin w × Bool) (B := Fin v × Bool)) l) := by
  have ha' : a ≤ finrank K (halfConstrainedSpace w j true T₁) * finrank K (Forms K v s) := by
    rw [finrank_forms K v s hv]
    exact ha.trans (Nat.mul_le_mul_right _ (halfConstrainedSpace_dimension hw j true T₁))
  have hb' : b ≤ finrank K (halfConstrainedSpace w l false T₂) * finrank K (Forms K v t) := by
    rw [finrank_forms K v t hv]
    exact hb.trans (Nat.mul_le_mul_right _ (halfConstrainedSpace_dimension hw l false T₂))
  obtain ⟨f,g,hf,hg,hi,hfm,hgm⟩ := exists_fourBlock_cross_pair
    (halfConstrainedSpace w j true T₁) (halfConstrainedSpace w l false T₂)
    (Forms K v s) (Forms K v t) inf_le_left inf_le_left le_rfl le_rfl ha' hb'
  refine ⟨f,g,?_,?_,hi,?_,?_⟩
  · intro i
    refine ⟨(hf i).1,(hf i).2.1,(hf i).2.2,?_⟩
    apply halfConstrainedSpace_output_kernel true T₁ (Forms K v s)
    convert hfm i using 1
    congr 3
    funext z
    cases z <;> rfl
  · intro i
    refine ⟨(hg i).1,(hg i).2.1,(hg i).2.2,?_⟩
    apply halfConstrainedSpace_output_kernel false T₂ (Forms K v t)
    convert hgm i using 1
    congr 3
    funext z
    cases z <;> rfl
  · intro i
    apply biformImage_half_output_weight true (halfConstrainedSpace w j true T₁) (Forms K v s) inf_le_left
    convert hfm i using 1
    congr 3
    funext z
    cases z <;> rfl
  · intro i
    apply biformImage_half_output_weight false (halfConstrainedSpace w l false T₂) (Forms K v t) inf_le_left
    convert hgm i using 1
    congr 3
    funext z
    cases z <;> rfl

end Froberg
