module

public import Froberg.ProductRows
public import Froberg.SeparatedRowKernel

@[expose] public section

/-! The first positive even row has no product columns. -/
noncomputable section
namespace Froberg
open Module
variable {K A B C V : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup V] [Module K V]

/-- Adjoining an empty formal source preserves exactness literally. -/
theorem addRow_exact_of_subsingleton [Subsingleton B]
    (f : A →ₗ[K] V) (g : B →ₗ[K] V) (Z : C →ₗ[K] A)
    (hZ : f.ker=Z.range) :
    (addRow f g).ker=((LinearMap.inl K A B).comp Z).range := by
  apply le_antisymm
  · rintro ⟨a,b⟩ hab
    have hb : b=0 := Subsingleton.elim _ _
    have ha : a∈Z.range := by
      rw [←hZ]
      change f a=0
      change f a+g b=0 at hab
      simpa only [hb,map_zero,add_zero] using hab
    obtain ⟨c,hc⟩ := ha
    exact ⟨c,by simp only [LinearMap.comp_apply,LinearMap.inl_apply,hc,hb]⟩
  · rintro x ⟨c,rfl⟩
    have hc : Z c∈f.ker := by rw [hZ]; exact ⟨c,rfl⟩
    change f (Z c)+g 0=0
    change f (Z c)=0 at hc
    simpa only [map_zero,add_zero] using hc

namespace ProductRows

theorem first_even_row_empty {J : Finset ℕ} (hJ : ∀ j∈J,2≤j) : IsEmpty (Row J 2) :=
  ⟨fun p => by
    have hl := hJ _ p.property.1
    have hr := hJ _ p.property.2.1
    have hp := p.property.2.2
    omega⟩

end ProductRows
end Froberg
