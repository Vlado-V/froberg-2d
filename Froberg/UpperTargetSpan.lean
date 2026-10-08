import Froberg.UpperTargetOpen

/-! Upper-target generation is preserved when the span of actual
polynomial generators grows. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {h m d r s : ℕ}

theorem upperTargetMap_surjective_of_span_le
    (Q : Fin r → Forms K (h+m) d) (F : Fin s → Forms K (h+m) d)
    (hspan : Submodule.span K (Set.range (fun i => (Q i).val))≤
      Submodule.span K (Set.range (fun i => (F i).val)))
    (hQ : Function.Surjective (upperTargetMap Q)) :
    Function.Surjective (upperTargetMap F) := by
  intro z
  obtain ⟨a,ha⟩ := hQ z
  have hmem : endpointMultiplication Q a∈(endpointMultiplication F).range := by
    rw [range_endpointMultiplication]
    have hqa : endpointMultiplication Q a∈(endpointMultiplication Q).range := ⟨a,rfl⟩
    rw [range_endpointMultiplication] at hqa
    exact (mul_le_mul' hspan le_rfl) hqa
  obtain ⟨b,hb⟩ := hmem
  refine ⟨b,?_⟩
  change (lowTargetSubspace (K := K) (h := h) (m := m) (d := d)).mkQ (endpointMultiplication F b)=z
  rw [hb]
  exact ha

end Froberg
