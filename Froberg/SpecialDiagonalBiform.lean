import Froberg.BiformWitnesses
import Froberg.QuadraticBlockSpace
import Froberg.QuarticBlockSpace

/-! The special diagonal witnesses in small degree use the full quadratic
or quartic output space, without an artificial output-half restriction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ τ : Type*}

/-- Symmetric-product independent output and scalar spaces give literal
biform columns with independent unordered products. -/
theorem exists_diagonal_sum_biforms
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    [Module.Finite K O] [Module.Finite K C]
    (hO : Function.Injective (subspaceSymmetricMultiplication O))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    {m : ℕ} (hm : m≤finrank K O*(finrank K C/2)) :
    ∃ f : Fin m → MvPolynomial (σ ⊕ τ) K,
      (∀ i,f i∈biformImage O C) ∧ LinearIndependent K (pairProducts f) := by
  obtain ⟨E,hE,hEd,hEi⟩ := separated_coefficient_space_exists O C hO hC hm
  letI : Module.Finite K E := Submodule.finiteDimensional_of_le hE
  subst m
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup K
  let b := Module.finBasis K E
  let e := MvPolynomial.tensorEquivSum K σ τ K
  let f := fun i : Fin (finrank K E) => e (b i).val
  refine ⟨f,fun i => ⟨(b i).val,hE (b i).property,rfl⟩,?_⟩
  have hp := (linearIndependent_pairProducts_in_subspace E hEi b b.linearIndependent).map'
    e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  convert hp using 1
  funext p
  induction p using Sym2.inductionOn with
  | _ i j => simp only [pairProducts_mk,Function.comp_apply,AlgEquiv.toLinearMap_apply,f,map_mul]

/-- Intersecting the output witness with a prescribed detector kernel loses
at most the detector target dimension. -/
theorem exists_constrained_diagonal_biforms
    {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
    (O : Submodule K (MvPolynomial σ K)) (C : Submodule K (MvPolynomial τ K))
    [Module.Finite K O] [Module.Finite K C]
    (hO : Function.Injective (subspaceSymmetricMultiplication O))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (T : MvPolynomial σ K →ₗ[K] X) {m : ℕ}
    (hm : m≤(finrank K O-finrank K X)*(finrank K C/2)) :
    ∃ f : Fin m → MvPolynomial (σ ⊕ τ) K,
      (∀ i,f i∈biformImage (O⊓T.ker) C) ∧ LinearIndependent K (pairProducts f) := by
  let O' := O⊓T.ker
  letI : Module.Finite K O' := Submodule.finiteDimensional_of_le (show O'≤O from inf_le_left)
  apply exists_diagonal_sum_biforms O' C
    (subspaceSymmetricMultiplication_injective_mono inf_le_left hO) hC
  exact hm.trans (Nat.mul_le_mul_right _ (finrank_intersection_kernel_lower_bound O T))

/-- The full span of the scalar variables has independent unordered products. -/
theorem linear_scalar_space_exists (n : ℕ) :
    ∃ C : Submodule K (MvPolynomial (Fin n) K),
      C≤Forms K n 1 ∧ finrank K C=n ∧
      Function.Injective (subspaceSymmetricMultiplication C) := by
  let C := Submodule.span K (Set.range (X : Fin n → MvPolynomial (Fin n) K))
  refine ⟨C,?_,?_,?_⟩
  · exact Submodule.span_le.mpr (by rintro p ⟨i,rfl⟩; exact isHomogeneous_X K i)
  · have hi : LinearIndependent K (X : Fin n → MvPolynomial (Fin n) K) :=
      linearIndependent_of_pairProducts _ (linearIndependent_pairProducts_X (K := K) (ι := Fin n))
    exact (finrank_span_eq_card hi).trans (Fintype.card_fin n)
  · exact symmetricMultiplication_injective_of_pairProducts
      (X : Fin n → MvPolynomial (Fin n) K) (linearIndependent_pairProducts_X (K := K) (ι := Fin n))

/-- The special quadratic diagonal capacity, with the full linear scalar
space used in degree three. -/
theorem quadratic_linear_diagonal_exists
    {h n m : ℕ} (hh : 65≤h)
    {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
    (T : Poly K h →ₗ[K] X) (hm : m≤(5*h^2/32-finrank K X)*(n/2)) :
    ∃ f : Fin m → MvPolynomial (Fin h ⊕ Fin n) K,
      (∀ i,f i∈biformImage (Forms K h 2⊓T.ker) (Forms K n 1)) ∧
      LinearIndependent K (pairProducts f) := by
  obtain ⟨O,hOh,hOd,hOi⟩ := QuadraticBlocks.quadratic_space_exists (K := K) hh
  obtain ⟨C,hCh,hCd,hCi⟩ := linear_scalar_space_exists (K := K) n
  letI : Module.Finite K O := Submodule.finiteDimensional_of_le hOh
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hCh
  obtain ⟨f,hf,hfi⟩ := exists_constrained_diagonal_biforms O C hOi hCi T
    (by simpa only [hOd,hCd] using hm)
  refine ⟨f,?_,hfi⟩
  intro i
  rcases hf i with ⟨a,⟨z,rfl⟩,ha⟩
  rw [←ha]
  refine ⟨_,⟨TensorProduct.map
    (Submodule.inclusion (show O⊓T.ker≤Forms K h 2⊓T.ker from inf_le_inf_right _ hOh))
    (Submodule.inclusion hCh) z,?_⟩,rfl⟩
  clear ha
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add,ha,hb]

end Froberg
