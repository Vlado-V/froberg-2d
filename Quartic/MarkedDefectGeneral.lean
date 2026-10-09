module

public import Quartic.MarkedCoefficient

@[expose] public section

/-! Exactness of the coefficient reader on abstract kernel quotients. -/
noncomputable section
namespace Quartic.MarkedDefectGeneral
open EndpointHomology MarkedCoefficient
variable {K V U W D : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [AddCommGroup D] [Module K D]

/-- A reduction modulo the new boundaries identifies the coefficient kernel
with the image of the old homology, without assuming the latter vanishes. -/
theorem coefficient_kernel_range
    (f : V →ₗ[K] W) (g : U →ₗ[K] W) (e : V →ₗ[K] U)
    (hcomm : g.comp e = f) (B : Submodule K V) (B' : Submodule K U)
    (hB : B ≤ B'.comap e) (c : U →ₗ[K] D) (C : Submodule K D)
    (hC : B' ≤ C.comap c)
    (hzero : ∀ x, c (e x) ∈ C)
    (hred : ∀ a, g a = 0 → c a ∈ C → ∃ b, f b = 0 ∧ a-e b ∈ B') :
    (quotientCoefficient g c B' C hC).ker =
      (inducedHomologyMap f g e hcomm B B' hB).range := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a,rfl⟩ := (kernelBoundary g B').mkQ_surjective z
    have hc : c a.val ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hz
    obtain ⟨b,hb,hred⟩ := hred a.val a.property hc
    refine ⟨(kernelBoundary f B).mkQ ⟨b,hb⟩,?_⟩
    change (kernelBoundary g B').mkQ (inducedCycleMap f g e hcomm ⟨b,hb⟩) =
      (kernelBoundary g B').mkQ a
    apply eq_of_sub_eq_zero
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change e b-a.val ∈ B'
    simpa only [neg_sub] using B'.neg_mem hred
  · rintro _ ⟨z,rfl⟩
    obtain ⟨b,rfl⟩ := (kernelBoundary f B).mkQ_surjective z
    change C.mkQ (c (e b.val)) = 0
    exact (Submodule.Quotient.mk_eq_zero C).mpr (hzero b.val)

end Quartic.MarkedDefectGeneral
