import Froberg.OddExtension

/-! The source of odd scalar contraction is unchanged when any even
homogeneous generator family is appended. The equivalence is the actual
map between the generator quotients. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {r t : ℕ}

theorem span_fin_append (q : Fin r → V) (f : Fin t → V) :
    Submodule.span K (Set.range (Fin.append q f))=
      Submodule.span K (Set.range q) ⊔ Submodule.span K (Set.range f) := by
  have h : Set.range (Fin.append q f)=Set.range q∪Set.range f := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      refine Fin.addCases ?_ ?_ i
      · intro j
        exact Or.inl ⟨j,by simp⟩
      · intro j
        exact Or.inr ⟨j,by simp⟩
    · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨Fin.castAdd t i,by simp⟩
      · exact ⟨Fin.natAdd r i,by simp⟩
  rw [h,Submodule.span_union]

variable {n d : ℕ}

def oddCoefficientExtensionEquiv
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (f : Fin t → Forms K n d) (hf : ∀ i,(f i).val.IsWeightedHomogeneous w 0) :
    oddCoefficientSpace w q ≃ₗ[K] oddCoefficientSpace w (Fin.append q f) := by
  unfold oddCoefficientSpace generatorQuotient
  rw [span_fin_append]
  apply projectedRangeExtensionEquiv
  · intro v
    exact parityForm_same w 1 _ (parityForm_homogeneous w 1 v)
  · exact fun v hv => parity_preserves_generator_span w e q hq 1 hv
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact parityForm_other w 1 0 (f i) (hf i) one_ne_zero

theorem oddCoefficientSpace_append_finrank
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (f : Fin t → Forms K n d) (hf : ∀ i,(f i).val.IsWeightedHomogeneous w 0) :
    finrank K (oddCoefficientSpace w (Fin.append q f))=finrank K (oddCoefficientSpace w q) :=
  (oddCoefficientExtensionEquiv w e q hq f hf).finrank_eq.symm

end Froberg
