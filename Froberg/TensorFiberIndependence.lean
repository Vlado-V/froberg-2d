module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

/-! Linear independence can be checked separately in the fibers of an
independent first tensor factor. -/
noncomputable section
open TensorProduct
namespace Froberg
variable {K : Type*} [Field K]
variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
variable {δ : Type*} [Fintype δ] {J : δ → Type*} [∀ d, Fintype (J d)]

theorem linearIndependent_tensor_fibers (o : δ → A) (ho : LinearIndependent K o)
    (q : (d : δ) → J d → B) (hq : ∀ d, LinearIndependent K (q d)) :
    LinearIndependent K (fun z : Sigma J => o z.1 ⊗ₜ[K] q z.1 z.2) := by
  classical
  obtain ⟨s,hs⟩ := (Finsupp.linearCombination K o).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ho)
  have hs_o (d : δ) : s (o d) = Finsupp.single d 1 := by
    have h := LinearMap.congr_fun hs (Finsupp.single d 1)
    simpa only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] using h
  let project (d : δ) : A →ₗ[K] K := (Finsupp.lapply d).comp s
  let T (d : δ) : A ⊗[K] B →ₗ[K] B :=
    (TensorProduct.lid K B).toLinearMap.comp (TensorProduct.map (project d) LinearMap.id)
  have hT (d e : δ) (b : B) : T d (o e ⊗ₜ[K] b) = if e = d then b else 0 := by
    simp only [T,LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_apply,
      LinearEquiv.coe_coe,TensorProduct.lid_tmul,project,hs_o,Finsupp.lapply_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  apply Fintype.linearIndependent_iff.mpr
  intro c hc z
  rcases z with ⟨d,j⟩
  apply Fintype.linearIndependent_iff.mp (hq d) (fun i => c ⟨d,i⟩) _ j
  have h := congrArg (T d) hc
  simp only [map_sum,map_smul,map_zero,hT] at h
  rw [Fintype.sum_sigma] at h
  have he : (∑ e, ∑ i : J e, c ⟨e,i⟩ • (if e = d then q e i else 0)) =
      ∑ i : J d, c ⟨d,i⟩ • q d i := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro e he hed
      simp [hed]
    · simp
  exact he.symm.trans h

end Froberg
