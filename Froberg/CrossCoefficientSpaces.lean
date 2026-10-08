import Froberg.GradedProductAssembly
import Froberg.SubspaceProductRestriction

/-! Exact finite-dimensional cross-pair capacities used in Lemma B.4. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K : Type} [Field K]
variable {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- The whole product of two coefficient-space dimensions is available for
an independent family in their tensor image. -/
theorem exists_independent_tensor_family (O : Submodule K A) (C : Submodule K B)
    [Module.Finite K O] [Module.Finite K C] {m : ℕ}
    (hm : m ≤ finrank K O * finrank K C) :
    ∃ q : Fin m → A ⊗[K] B,
      (∀ i, q i ∈ LinearMap.range (TensorProduct.map O.subtype C.subtype)) ∧
      LinearIndependent K q := by
  classical
  let bo := Module.finBasis K O
  let bc := Module.finBasis K C
  let a : Fin (finrank K O) → A := fun i => (bo i).val
  let b : Fin (finrank K C) → B := fun i => (bc i).val
  have ha : LinearIndependent K a := bo.linearIndependent.map' O.subtype
    (LinearMap.ker_eq_bot.mpr O.subtype_injective)
  have hb : LinearIndependent K b := bc.linearIndependent.map' C.subtype
    (LinearMap.ker_eq_bot.mpr C.subtype_injective)
  have hi := linearIndependent_cross_tensors a b ha hb
  obtain ⟨e⟩ : Nonempty (Fin m ↪ (Fin (finrank K O) × Fin (finrank K C))) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  refine ⟨fun i => a (e i).1 ⊗ₜ[K] b (e i).2,?_,hi.comp e e.injective⟩
  intro i
  exact ⟨bo (e i).1 ⊗ₜ[K] bc (e i).2,rfl⟩

/-- Cross-pair coefficient spaces provide actual independent homogeneous
polynomials in disjoint variable blocks. -/
theorem exists_independent_biforms {h n j t m : ℕ}
    (O : Submodule K (Poly K h)) (C : Submodule K (Poly K n))
    (hO : O ≤ Forms K h j) (hC : C ≤ Forms K n t)
    (hm : m ≤ finrank K O * finrank K C) :
    ∃ q : Fin m → Forms K (h+n) (j+t), LinearIndependent K q ∧
      ∀ i, (q i).val ∈ (LinearMap.range (TensorProduct.map O.subtype C.subtype)).map
        (splitPolynomialEquiv (K := K) h n).toLinearMap := by
  letI : Module.Finite K O := Submodule.finiteDimensional_of_le hO
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hC
  obtain ⟨a,ha,hai⟩ := exists_independent_tensor_family O C hm
  let e := splitPolynomialEquiv (K := K) h n
  have ha' (i) : e (a i) ∈ Forms K (h+n) (j+t) :=
    splitPolynomialEquiv_range_homogeneous O C hO hC ⟨a i,ha i,rfl⟩
  let q : Fin m → Forms K (h+n) (j+t) := fun i => ⟨e (a i),ha' i⟩
  refine ⟨q,?_,fun i => ⟨a i,ha i,rfl⟩⟩
  apply LinearIndependent.of_comp (Forms K (h+n) (j+t)).subtype
  exact hai.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

/-- A finite set of output equations costs at most one output dimension
per equation, including when the ambient polynomial ring is infinite. -/
theorem exists_independent_biforms_with_output_constraint
    {h n j t m : ℕ} (hh : 0 < h) (hn : 0 < n)
    {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
    (T : Poly K h →ₗ[K] X)
    (hm : m ≤ ((h+j-1).choose j - finrank K X) * (n+t-1).choose t) :
    ∃ q : Fin m → Forms K (h+n) (j+t), LinearIndependent K q ∧
      ∀ i, (q i).val ∈ (LinearMap.range (TensorProduct.map
        (Forms K h j ⊓ T.ker).subtype (Forms K n t).subtype)).map
          (splitPolynomialEquiv (K := K) h n).toLinearMap := by
  apply exists_independent_biforms (Forms K h j ⊓ T.ker) (Forms K n t) inf_le_left le_rfl
  have hdim := finrank_intersection_kernel_lower_bound (Forms K h j) T
  rw [finrank_forms K h j hh] at hdim
  rw [finrank_forms K n t hn]
  exact hm.trans (Nat.mul_le_mul_right _ hdim)

end Froberg
