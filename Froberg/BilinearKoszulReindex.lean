import Froberg.BilinearKoszulRow

/-! Literal row exactness does not depend on how either finite generator list
is enumerated. -/
noncomputable section
namespace Froberg
open Module
variable {K U V A W I J I' J' : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup A] [Module K A]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

/-- Reindex both the scalar and the new-layer generators. -/
theorem bilinearKoszulRow_exact_reindex (eI : I' ≃ I) (eJ : J' ≃ J)
    (μ : V →ₗ[K] U →ₗ[K] A) (Q : I → V) (E : J → U) (P : W →ₗ[K] A)
    (hexact : (bilinearKoszulRow μ Q E P).ker=
      (bilinearKoszulConstants (K := K) (W := W) Q E).range) :
    (bilinearKoszulRow μ (Q ∘ eI) (E ∘ eJ) P).ker=
      (bilinearKoszulConstants (K := K) (W := W) (Q ∘ eI) (E ∘ eJ)).range := by
  apply le_antisymm
  · intro x hx
    let y : ((I → U) × (J → V)) × W :=
      ((x.1.1 ∘ eI.symm,x.1.2 ∘ eJ.symm),x.2)
    have hy : y∈(bilinearKoszulRow μ Q E P).ker := by
      change (∑ i,μ (Q (eI i)) (x.1.1 i))+(∑ j,μ (x.1.2 j) (E (eJ j)))+P x.2=0 at hx
      change (∑ i,μ (Q i) (x.1.1 (eI.symm i)))+
        (∑ j,μ (x.1.2 (eJ.symm j)) (E j))+P x.2=0
      rw [← eI.sum_comp,← eJ.sum_comp]
      simpa only [Equiv.symm_apply_apply] using hx
    rw [hexact] at hy
    obtain ⟨C,hC⟩ := hy
    refine ⟨fun i j => C (eI i) (eJ j),?_⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        have hi := congrArg (fun z : ((I → U) × (J → V)) × W => z.1.1 (eI i)) hC
        change (∑ j,C (eI i) (eJ j) • E (eJ j))=x.1.1 i
        rw [eJ.sum_comp (fun j => C (eI i) j • E j)]
        change (∑ j,C (eI i) j • E j)=x.1.1 (eI.symm (eI i)) at hi
        simpa only [Equiv.symm_apply_apply] using hi
      · funext j
        have hj := congrArg (fun z : ((I → U) × (J → V)) × W => z.1.2 (eJ j)) hC
        change -(∑ i,C (eI i) (eJ j) • Q (eI i))=x.1.2 j
        rw [eI.sum_comp (fun i => C i (eJ j) • Q i)]
        change -(∑ i,C i (eJ j) • Q i)=x.1.2 (eJ.symm (eJ j)) at hj
        simpa only [Equiv.symm_apply_apply] using hj
    · exact congrArg (fun z : ((I → U) × (J → V)) × W => z.2) hC
  · rintro x ⟨C,rfl⟩
    exact LinearMap.congr_fun (bilinearKoszulRow_constants μ (Q ∘ eI) (E ∘ eJ) P) C

end Froberg
