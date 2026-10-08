import Froberg.PolynomialTensorTransport
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! The two independence mechanisms in the product part of Lemma B.4:
disjoint-variable cross products, and assembly in distinct half-degrees. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K]

/-- Independent polynomial fibers in distinct weight degrees have an
independent union. No dimensions are discarded in assembling product rows. -/
theorem linearIndependent_weighted_fibers {σ M δ : Type*} [AddCommMonoid M]
    [Fintype δ] {I : δ → Type*} [∀ d, Fintype (I d)]
    (w : σ → M) (degree : δ → M) (hdegree : Function.Injective degree)
    (q : (d : δ) → I d → MvPolynomial σ K)
    (hq : ∀ d, LinearIndependent K (q d))
    (hhom : ∀ d i, (q d i).IsWeightedHomogeneous w (degree d)) :
    LinearIndependent K (fun z : Sigma I => q z.1 z.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc z
  rcases z with ⟨d,i⟩
  apply Fintype.linearIndependent_iff.mp (hq d) (fun j => c ⟨d,j⟩) _ i
  have h := congrArg (weightedHomogeneousComponent w (degree d)) hc
  simp only [map_sum,map_smul,map_zero] at h
  rw [Fintype.sum_sigma] at h
  have he (e : δ) (j : I e) :
      weightedHomogeneousComponent w (degree d) (q e j) = if e=d then q e j else 0 := by
    rw [weightedHomogeneousComponent_of_mem (hhom e j)]
    simp only [hdegree.eq_iff,eq_comm]
  simp_rw [he] at h
  simpa using h

/-- Tensor products of two independent finite families are independent. -/
theorem linearIndependent_cross_tensors {A B α β : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [Fintype α] [Fintype β] (a : α → A) (b : β → B)
    (ha : LinearIndependent K a) (hb : LinearIndependent K b) :
    LinearIndependent K (fun p : α × β => a p.1 ⊗ₜ[K] b p.2) := by
  have h := linearIndependent_tensor_fibers a ha (fun _ => b) (fun _ => hb)
  let f (p : α × β) : Σ _ : α, β := ⟨p.1,p.2⟩
  have hf : Function.Injective f := by
    intro p q h
    have h1 := congrArg Sigma.fst h
    have h2 := congrArg (fun z : Σ _ : α, β => z.2) h
    exact Prod.ext h1 h2
  exact h.comp f hf

/-- Cross products of independent families supported in disjoint variables
are independent in the actual polynomial ring. -/
theorem linearIndependent_cross_products_disjoint {σ τ α β : Type*}
    [Fintype α] [Fintype β]
    (a : α → MvPolynomial σ K) (b : β → MvPolynomial τ K)
    (ha : LinearIndependent K a) (hb : LinearIndependent K b) :
    LinearIndependent K (fun p : α × β =>
      rename Sum.inl (a p.1) * rename Sum.inr (b p.2)) := by
  have h := (linearIndependent_cross_tensors a b ha hb).map'
    (MvPolynomial.tensorEquivSum K σ τ K).toLinearMap
    (LinearMap.ker_eq_bot.mpr (MvPolynomial.tensorEquivSum K σ τ K).injective)
  convert h using 1
  funext p
  exact (tensorEquivSum_tmul (a p.1) (b p.2)).symm

end Froberg
