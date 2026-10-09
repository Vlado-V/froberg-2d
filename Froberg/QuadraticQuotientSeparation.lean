module

public import Froberg.PolynomialTensorTransport

@[expose] public section

/-! The tensor separation construction inside the actual homogeneous
polynomial spaces, with the precise formal-product conclusion used in C.6. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg
open Module TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h n j t m : ℕ}

/-- Pointwise annihilation of old polynomial products annihilates the full
formal mixed-product image. -/
theorem formalMixed_polynomial_map_le_ker (W : Submodule K (Forms K n j))
    (T : Poly K n →ₗ[K] X)
    (hW : ∀ w : Forms K n j, w ∈ W → ∀ a : Forms K n j, T (w.val*a.val) = 0) :
    (formalMixed W).map formalPolynomialMultiplication ≤
      (T.comp (Forms K n (2*j)).subtype).ker := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨a,b,ha,rfl⟩
  change T ((formalPolynomialMultiplication (symProd a b)).val) = 0
  rw [formalPolynomialMultiplication_symProd]
  exact hW a ha b

/-- The tensor-space construction supplies actual homogeneous forms with
independent products after the output/scalar detector. -/
theorem exists_detected_homogeneous_family
    (o : ι → Forms K h j) (T : Poly K h →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)))
    (C P Q : Submodule K (Poly K n)) (hCt : C ≤ Forms K n t)
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCP : C*C ≤ P) (hPQ : Disjoint P Q)
    (hm : m ≤ Fintype.card ι * (finrank K C / 2)) :
    ∃ f : Fin m → Forms K (h+n) (j+t),
      LinearIndependent K (fun p => splitPolynomialDetector T Q
        ((formalPolynomialMultiplication (formalPair (K := K) f p)).val)) := by
  classical
  letI : Module.Finite K C := Submodule.finiteDimensional_of_le hCt
  let o' : ι → Poly K h := fun i => (o i).val
  obtain ⟨q,hq,hp⟩ := exists_detected_separated_family o' T ho C P Q hC hCP hPQ hm
  let e := splitPolynomialEquiv (K := K) h n
  have hOh : Submodule.span K (Set.range o') ≤ Forms K h j :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (o i).property)
  have hhom (i : Fin m) : e (q i) ∈ Forms K (h+n) (j+t) :=
    splitPolynomialEquiv_range_homogeneous _ _ hOh hCt ⟨q i,hq i,rfl⟩
  let f : Fin m → Forms K (h+n) (j+t) := fun i => ⟨e (q i),hhom i⟩
  refine ⟨f,?_⟩
  convert hp using 1
  funext p
  induction p using Sym2.inductionOn with
  | _ i k =>
    simp only [formalPair_mk,formalPolynomialMultiplication_symProd,pairProducts_mk]
    change splitPolynomialDetector T Q (e (q i) * e (q k)) =
      TensorProduct.map T Q.mkQ (q i * q k)
    rw [← map_mul]
    simp only [splitPolynomialDetector,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
      e,AlgEquiv.symm_apply_apply]

/-- Appendix C.2's separation conclusion, in actual homogeneous polynomial
spaces. Taking j=1 and t=d−1 gives exactly the new generator family F. -/
theorem exists_separated_homogeneous_family
    (o : ι → Forms K h j) (T : Poly K h →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)))
    (C P Q : Submodule K (Poly K n)) (hCt : C ≤ Forms K n t)
    (hC : Function.Injective (subspaceSymmetricMultiplication C))
    (hCP : C*C ≤ P) (hPQ : Disjoint P Q)
    (hm : m ≤ Fintype.card ι * (finrank K C / 2)) :
    ∃ f : Fin m → Forms K (h+n) (j+t),
      LinearIndependent K f ∧ finrank K (Submodule.span K (Set.range f)) = m ∧
      ∀ W : Submodule K (Forms K (h+n) (j+t)),
        (∀ w : Forms K (h+n) (j+t), w ∈ W → ∀ a : Forms K (h+n) (j+t),
          splitPolynomialDetector T Q (w.val*a.val) = 0) →
        formalSquare (Submodule.span K (Set.range f)) ⊓
          ((formalMixed W).map formalPolynomialMultiplication).comap
            (formalPolynomialMultiplication (K := K) (n := h+n) (d := j+t)) = ⊥ := by
  obtain ⟨f,hf⟩ := exists_detected_homogeneous_family o T ho C P Q hCt hC hCP hPQ hm
  have hprod : LinearIndependent K (pairProducts (fun i => (f i).val)) := by
    apply LinearIndependent.of_comp (splitPolynomialDetector T Q)
    convert hf using 1
    funext p
    induction p using Sym2.inductionOn with
    | _ i k =>
      simp only [Function.comp_apply,pairProducts_mk,formalPair_mk,formalPolynomialMultiplication_symProd]
      rfl
  have hfi : LinearIndependent K f := by
    apply LinearIndependent.of_comp (Forms K (h+n) (j+t)).subtype
    exact linearIndependent_of_pairProducts (fun i => (f i).val) hprod
  refine ⟨f,hfi,?_,?_⟩
  · rw [finrank_span_eq_card hfi,Fintype.card_fin]
  · intro W hW
    exact formalSquare_separated_from_mixed_of_detected_products
      formalPolynomialMultiplication
      ((splitPolynomialDetector T Q).comp (Forms K (h+n) (2*(j+t))).subtype)
      W (formalMixed_polynomial_map_le_ker W _ hW) f hf

end Froberg
