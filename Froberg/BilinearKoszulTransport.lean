import Froberg.BilinearKoszulRow

/-! Exact scalar/new-layer rows are independent of the chosen complete
coordinates in the output coefficient space. -/
noncomputable section
namespace Froberg
open Module
variable {K U U' V A W I J : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup U'] [Module K U'] [FiniteDimensional K U']
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup A] [Module K A]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [Fintype I] [Fintype J]

/-- Transport a literal exact row along a complete change of output coordinates. -/
theorem bilinearKoszulRow_exact_transport
    (e : U ≃ₗ[K] U') (μ : V →ₗ[K] U →ₗ[K] A)
    (μ' : V →ₗ[K] U' →ₗ[K] A)
    (hμ : ∀ v u,μ' v (e u)=μ v u)
    (Q : I → V) (E : J → U) (P : W →ₗ[K] A)
    (hexact : (bilinearKoszulRow μ Q E P).ker=
      (bilinearKoszulConstants (K := K) (W := W) Q E).range) :
    (bilinearKoszulRow μ' Q (fun j => e (E j)) P).ker=
      (bilinearKoszulConstants (K := K) (W := W) Q (fun j => e (E j))).range := by
  apply le_antisymm
  · intro x hx
    let y : ((I → U) × (J → V)) × W :=
      ((fun i => e.symm (x.1.1 i),x.1.2),x.2)
    have hy : y∈(bilinearKoszulRow μ Q E P).ker := by
      change (∑ i,μ (Q i) (e.symm (x.1.1 i)))+
        (∑ j,μ (x.1.2 j) (E j))+P x.2=0
      change (∑ i,μ' (Q i) (x.1.1 i))+
        (∑ j,μ' (x.1.2 j) (e (E j)))+P x.2=0 at hx
      simpa only [←hμ,LinearEquiv.apply_symm_apply] using hx
    rw [hexact] at hy
    obtain ⟨C,hC⟩ := hy
    refine ⟨C,?_⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        have hi := congrArg (fun z : ((I → U) × (J → V)) × W => z.1.1 i) hC
        have hi' := congrArg e hi
        change e (∑ j,C i j • E j)=e (e.symm (x.1.1 i)) at hi'
        change (∑ j,C i j • e (E j))=x.1.1 i
        simpa only [map_sum,map_smul,LinearEquiv.apply_symm_apply] using hi'
      · exact congrArg (fun z : ((I → U) × (J → V)) × W => z.1.2) hC
    · exact congrArg (fun z : ((I → U) × (J → V)) × W => z.2) hC
  · rintro x ⟨C,rfl⟩
    exact LinearMap.congr_fun (bilinearKoszulRow_constants μ' Q (fun j => e (E j)) P) C

end Froberg
