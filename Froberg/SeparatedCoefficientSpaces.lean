import Froberg.SeparatedScalarFamilies
import Froberg.TensorFiberIndependence
import Mathlib.RingTheory.TensorProduct.Basic

/-! Lemma A.4: pairwise separated scalar coefficient spaces provide the full
stated capacity for independent symmetric products in a tensor product. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K : Type} [Field K]
variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def tensorFamily (o : ι → A) (c : ι × Fin r → B) : ι × Fin r → A ⊗[K] B :=
  fun i => o i.1 ⊗ₜ[K] c i

theorem pairProducts_tensorFamily (o : ι → A) (c : ι × Fin r → B)
    (p : Sym2 (ι × Fin r)) :
    pairProducts (tensorFamily (K := K) o c) p =
      pairProducts o (Sym2.map Prod.fst p) ⊗ₜ[K] pairProducts c p := by
  induction p using Sym2.inductionOn with
  | _ i j =>
    simp only [pairProducts_mk, tensorFamily, Sym2.map_mk,
      Algebra.TensorProduct.tmul_mul_tmul]

/-- Output-pair independence separates all scalar pair fibers. -/
theorem linearIndependent_tensorFamily_products (o : ι → A)
    (ho : LinearIndependent K (pairProducts o)) (c : ι × Fin r → B)
    (hc : ∀ δ : Sym2 ι, LinearIndependent K
      (fun p : ScalarPairFiber (r := r) δ => pairProducts c p.val)) :
    LinearIndependent K (pairProducts (tensorFamily (K := K) o c)) := by
  classical
  have h := linearIndependent_tensor_fibers (pairProducts o) ho
    (fun δ (p : ScalarPairFiber (r := r) δ) => pairProducts c p.val) hc
  let f (p : Sym2 (ι × Fin r)) : Σ δ : Sym2 ι, ScalarPairFiber (r := r) δ :=
    ⟨Sym2.map Prod.fst p, ⟨p,rfl⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    exact congrArg (fun z : Σ δ : Sym2 ι, ScalarPairFiber (r := r) δ => z.2.val) h
  have h' := h.comp f hf
  convert h' using 1
  funext p
  exact pairProducts_tensorFamily (K := K) o c p

/-- A basis of each output space and full-spark scalar groups give every
number of independent products up to the separated coefficient capacity. -/
theorem exists_separated_coefficient_family [Infinite K]
    (O : Submodule K A) (C : Submodule K B) [Module.Finite K O] [Module.Finite K C]
    (hO : Function.Injective (subspaceSymmetricMultiplication O))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    {m : ℕ} (hm : m ≤ finrank K O * (finrank K C / 2)) :
    ∃ q : Fin m → A ⊗[K] B,
      (∀ i, q i ∈ LinearMap.range (TensorProduct.map O.subtype C.subtype)) ∧
      LinearIndependent K (pairProducts q) := by
  classical
  let b := Module.finBasis K O
  let o : Fin (finrank K O) → A := fun i => (b i).val
  have ho : LinearIndependent K (pairProducts o) :=
    linearIndependent_pairProducts_in_subspace O hO b b.linearIndependent
  obtain ⟨c,hc⟩ := exists_scalar_pair_fiber_independent (ι := Fin (finrank K O))
    (r := finrank K C / 2) C hC (by omega)
  let c' : Fin (finrank K O) × Fin (finrank K C / 2) → B := fun i => (c i).val
  have hp : LinearIndependent K (pairProducts (tensorFamily (K := K) o c')) :=
    linearIndependent_tensorFamily_products o ho c' hc
  obtain ⟨e⟩ : Nonempty (Fin m ↪ (Fin (finrank K O) × Fin (finrank K C / 2))) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  let q : Fin m → A ⊗[K] B := fun i => tensorFamily (K := K) o c' (e i)
  refine ⟨q, ?_, ?_⟩
  · intro i
    refine ⟨b (e i).1 ⊗ₜ[K] c (e i), ?_⟩
    rfl
  · have h := hp.comp (Sym2.map e) (Sym2.map.injective e.injective)
    convert h using 1
    funext p
    exact (pairProducts_map (tensorFamily (K := K) o c') e p).symm

/-- Lemma A.4, as an actual subspace of the tensor-product algebra. -/
theorem separated_coefficient_space_exists [Infinite K]
    (O : Submodule K A) (C : Submodule K B) [Module.Finite K O] [Module.Finite K C]
    (hO : Function.Injective (subspaceSymmetricMultiplication O))
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    {m : ℕ} (hm : m ≤ finrank K O * (finrank K C / 2)) :
    ∃ E : Submodule K (A ⊗[K] B),
      E ≤ LinearMap.range (TensorProduct.map O.subtype C.subtype) ∧
      finrank K E = m ∧ Function.Injective (subspaceSymmetricMultiplication E) := by
  obtain ⟨q,hq,hp⟩ := exists_separated_coefficient_family O C hO hC hm
  refine ⟨Submodule.span K (Set.range q), ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hq i)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hp), Fintype.card_fin]
  · exact symmetricMultiplication_injective_of_pairProducts q hp

end Froberg
