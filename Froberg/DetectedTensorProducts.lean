import Froberg.SeparatedCoefficientSpaces
import Froberg.DetectedSymmetricProducts

/-! Scalar disjointness and independent output products give genuine
symmetric-product separation after quotienting a tensor factor. -/
noncomputable section
namespace Froberg
open Module TensorProduct
variable {K : Type} [Field K]
variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
variable {X : Type*} [AddCommGroup X] [Module K X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- The scalar quotient preserves each independent output-pair fiber when
all scalar products lie in a space disjoint from the scalar relations. -/
theorem scalar_pair_fiber_independent_quotient (c : ι × Fin r → B)
    (hc : ∀ δ : Sym2 ι, LinearIndependent K
      (fun p : ScalarPairFiber (r := r) δ => pairProducts c p.val))
    (P Q : Submodule K B) (hPQ : Disjoint P Q)
    (hP : ∀ p, pairProducts c p ∈ P) (δ : Sym2 ι) :
    LinearIndependent K (fun p : ScalarPairFiber (r := r) δ => Q.mkQ (pairProducts c p.val)) := by
  have hi : Set.InjOn Q.mkQ P := LinearMap.disjoint_ker_iff_injOn.mp (by simpa using hPQ)
  exact (hc δ).map_injOn Q.mkQ (hi.mono (Submodule.span_le.mpr (by
    rintro _ ⟨p,rfl⟩
    exact hP p.val)))

/-- The detected products in a tensor quotient are independent. This is the
linear-algebra part of the quadratic separation argument in Appendix C.2. -/
theorem linearIndependent_detected_tensor_products
    (o : ι → A) (T : A →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts o p)))
    (c : ι × Fin r → B)
    (hc : ∀ δ : Sym2 ι, LinearIndependent K
      (fun p : ScalarPairFiber (r := r) δ => pairProducts c p.val))
    (P Q : Submodule K B) (hPQ : Disjoint P Q)
    (hP : ∀ p, pairProducts c p ∈ P) :
    LinearIndependent K (fun p => TensorProduct.map T Q.mkQ
      (pairProducts (tensorFamily (K := K) o c) p)) := by
  classical
  have h := linearIndependent_tensor_fibers (fun p => T (pairProducts o p)) ho
    (fun δ (p : ScalarPairFiber (r := r) δ) => Q.mkQ (pairProducts c p.val))
    (scalar_pair_fiber_independent_quotient c hc P Q hPQ hP)
  let f (p : Sym2 (ι × Fin r)) : Σ δ : Sym2 ι, ScalarPairFiber (r := r) δ :=
    ⟨Sym2.map Prod.fst p, ⟨p,rfl⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    exact congrArg (fun z : Σ δ : Sym2 ι, ScalarPairFiber (r := r) δ => z.2.val) h
  have h' := h.comp f hf
  convert h' using 1
  funext p
  rw [pairProducts_tensorFamily, TensorProduct.map_tmul]
  rfl

/-- Choose the scalar groups needed for the detected tensor-product
construction; the only dimension bound is twice the group size. -/
theorem exists_detected_tensor_family [Infinite K]
    (o : ι → A) (T : A →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts o p)))
    (C P Q : Submodule K B) [Module.Finite K C]
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCP : C*C ≤ P) (hPQ : Disjoint P Q) (hr : 2*r ≤ finrank K C) :
    ∃ c : ι × Fin r → C, LinearIndependent K (fun p => TensorProduct.map T Q.mkQ
      (pairProducts (tensorFamily (K := K) o (fun i => (c i).val)) p)) := by
  obtain ⟨c,hc⟩ := exists_scalar_pair_fiber_independent (ι := ι) C hC hr
  refine ⟨c, linearIndependent_detected_tensor_products o T ho _ hc P Q hPQ ?_⟩
  intro p
  induction p using Sym2.inductionOn with
  | _ i j => exact hCP (Submodule.mul_mem_mul (c i).property (c j).property)

/-- Every dimension up to the separated coefficient capacity is attained by
an actual tensor family whose symmetric products survive the detector. -/
theorem exists_detected_separated_family [Infinite K]
    (o : ι → A) (T : A →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts o p)))
    (C P Q : Submodule K B) [Module.Finite K C]
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCP : C*C ≤ P) (hPQ : Disjoint P Q) {m : ℕ}
    (hm : m ≤ Fintype.card ι * (finrank K C / 2)) :
    ∃ q : Fin m → A ⊗[K] B,
      (∀ i, q i ∈ LinearMap.range (TensorProduct.map
        (Submodule.span K (Set.range o)).subtype C.subtype)) ∧
      LinearIndependent K (fun p => TensorProduct.map T Q.mkQ (pairProducts q p)) := by
  classical
  obtain ⟨c,hc⟩ := exists_detected_tensor_family (r := finrank K C / 2)
    o T ho C P Q hC hCP hPQ (by omega)
  obtain ⟨e⟩ : Nonempty (Fin m ↪ (ι × Fin (finrank K C / 2))) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  let q : Fin m → A ⊗[K] B := fun i =>
    tensorFamily (K := K) o (fun j => (c j).val) (e i)
  refine ⟨q, ?_, ?_⟩
  · intro i
    refine ⟨(⟨o (e i).1, Submodule.subset_span ⟨(e i).1,rfl⟩⟩ :
      Submodule.span K (Set.range o)) ⊗ₜ[K] c (e i), rfl⟩
  · have h := hc.comp (Sym2.map e) (Sym2.map.injective e.injective)
    convert h using 1
    funext p
    simp only [Function.comp_apply, pairProducts_map]
    rfl

/-- Actual tensor-algebra version of quadratic separation: it supplies the
exact formal-square condition required by the homology coefficient map. -/
theorem exists_separated_tensor_space [Infinite K]
    (o : ι → A) (T : A →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts o p)))
    (C P Q : Submodule K B) [Module.Finite K C]
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCP : C*C ≤ P) (hPQ : Disjoint P Q)
    (J : Submodule K (A ⊗[K] B)) (hJ : J ≤ (TensorProduct.map T Q.mkQ).ker)
    {m : ℕ} (hm : m ≤ Fintype.card ι * (finrank K C / 2)) :
    ∃ q : Fin m → A ⊗[K] B,
      (∀ i, q i ∈ LinearMap.range (TensorProduct.map
        (Submodule.span K (Set.range o)).subtype C.subtype)) ∧
      finrank K (Submodule.span K (Set.range q)) = m ∧
      formalSquare (Submodule.span K (Set.range q)) ⊓
        J.comap symmetricMultiplication = ⊥ := by
  obtain ⟨q,hq,hp⟩ := exists_detected_separated_family o T ho C P Q hC hCP hPQ hm
  have hp' : LinearIndependent K (pairProducts q) :=
    LinearIndependent.of_comp (TensorProduct.map T Q.mkQ) hp
  refine ⟨q,hq,?_,?_⟩
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hp'), Fintype.card_fin]
  · apply formalSquare_separated_of_detected_products symmetricMultiplication
      (TensorProduct.map T Q.mkQ) J hJ q
    convert hp using 1
    funext p
    induction p using Sym2.inductionOn with | _ i j => simp

end Froberg
