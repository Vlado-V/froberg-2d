import Froberg.DetectedTensorProducts
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! Transport the tensor-algebra constructions to the actual polynomial ring
in the disjoint union of two finite variable sets. -/
noncomputable section
namespace Froberg
open Module TensorProduct MvPolynomial
variable {K : Type} [Field K]
variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- An injective algebra map preserves the independent symmetric-product
property of every finite-dimensional subspace. -/
theorem subspaceSymmetricMultiplication_map_injective (f : A →ₐ[K] B)
    (hf : Function.Injective f) (E : Submodule K A) [Module.Finite K E]
    (hE : Function.Injective (subspaceSymmetricMultiplication E)) :
    Function.Injective (subspaceSymmetricMultiplication (E.map f.toLinearMap)) := by
  classical
  let b := Module.finBasis K E
  let q : Fin (finrank K E) → A := fun i => (b i).val
  have hq : LinearIndependent K (pairProducts q) :=
    linearIndependent_pairProducts_in_subspace E hE b b.linearIndependent
  have hspan : Submodule.span K (Set.range q) = E := by
    calc
      Submodule.span K (Set.range q) = (Submodule.span K (Set.range b)).map E.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = E := by rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hp : LinearIndependent K (pairProducts (f ∘ q)) := by
    have h := hq.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr hf)
    convert h using 1
    funext p
    induction p using Sym2.inductionOn with | _ i j => simp [Function.comp_def]
  have hspan' : Submodule.span K (Set.range (f ∘ q)) = E.map f.toLinearMap := by
    calc
      Submodule.span K (Set.range (f ∘ q)) =
          (Submodule.span K (Set.range q)).map f.toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = E.map f.toLinearMap := congrArg (Submodule.map f.toLinearMap) hspan
  rw [← hspan']
  exact symmetricMultiplication_injective_of_pairProducts _ hp

variable {σ τ : Type*}

/-- The polynomial tensor equivalence acts on a pure tensor by multiplying
the two disjoint-variable renamings. -/
theorem tensorEquivSum_tmul (a : MvPolynomial σ K) (b : MvPolynomial τ K) :
    MvPolynomial.tensorEquivSum K σ τ K (a ⊗ₜ[K] b) =
      rename Sum.inl a * rename Sum.inr b := by
  let e := MvPolynomial.tensorEquivSum K σ τ K
  have hl : e.toAlgHom.comp (Algebra.TensorProduct.includeLeft :
      MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⊗[K] MvPolynomial τ K) = rename Sum.inl := by
    ext i
    simp [e]
  have hr : e.toAlgHom.comp (Algebra.TensorProduct.includeRight :
      MvPolynomial τ K →ₐ[K] MvPolynomial σ K ⊗[K] MvPolynomial τ K) = rename Sum.inr := by
    ext i
    simp [e]
  have hla : e (a ⊗ₜ[K] (1 : MvPolynomial τ K)) = rename Sum.inl a := AlgHom.congr_fun hl a
  have hrb : e ((1 : MvPolynomial σ K) ⊗ₜ[K] b) = rename Sum.inr b := AlgHom.congr_fun hr b
  change e (a ⊗ₜ[K] b) = _
  calc
    e (a ⊗ₜ[K] b) = e ((a ⊗ₜ[K] 1) * (1 ⊗ₜ[K] b)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := by rw [map_mul,hla,hrb]

/-- Split polynomial coordinates with the manuscript's ordinary Fin(h+n)
variable indexing. -/
def splitPolynomialEquiv (h n : ℕ) :
    Poly K h ⊗[K] Poly K n ≃ₐ[K] Poly K (h+n) :=
  (MvPolynomial.tensorEquivSum K (Fin h) (Fin n) K).trans
    (MvPolynomial.renameEquiv K finSumFinEquiv)

@[simp] theorem splitPolynomialEquiv_tmul {h n : ℕ} (a : Poly K h) (b : Poly K n) :
    splitPolynomialEquiv (K := K) h n (a ⊗ₜ[K] b) =
      rename (Fin.castAdd n) a * rename (Fin.natAdd h) b := by
  change rename finSumFinEquiv (MvPolynomial.tensorEquivSum K (Fin h) (Fin n) K (a ⊗ₜ[K] b)) = _
  rw [tensorEquivSum_tmul,map_mul,rename_rename,rename_rename]
  rfl

/-- Homogeneous tensor factors multiply to forms of the sum degree. -/
theorem splitPolynomialEquiv_tmul_homogeneous {h n j t : ℕ}
    (a : Forms K h j) (b : Forms K n t) :
    splitPolynomialEquiv (K := K) h n (a.val ⊗ₜ[K] b.val) ∈ Forms K (h+n) (j+t) := by
  rw [splitPolynomialEquiv_tmul]
  exact a.property.rename_isHomogeneous.mul b.property.rename_isHomogeneous

/-- The tensor image of any two homogeneous subspaces is homogeneous. -/
theorem splitPolynomialEquiv_range_homogeneous {h n j t : ℕ}
    (O : Submodule K (Poly K h)) (C : Submodule K (Poly K n))
    (hO : O ≤ Forms K h j) (hC : C ≤ Forms K n t) :
    (LinearMap.range (TensorProduct.map O.subtype C.subtype)).map
      (splitPolynomialEquiv (K := K) h n).toLinearMap ≤ Forms K (h+n) (j+t) := by
  rintro x ⟨y,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    exact splitPolynomialEquiv_tmul_homogeneous ⟨a.val,hO a.property⟩ ⟨b.val,hC b.property⟩
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

variable {X : Type*} [AddCommGroup X] [Module K X]

/-- The output-and-scalar-quotient detector on the actual full polynomial ring. -/
def splitPolynomialDetector {h n : ℕ} (T : Poly K h →ₗ[K] X)
    (Q : Submodule K (Poly K n)) : Poly K (h+n) →ₗ[K] X ⊗[K] (Poly K n ⧸ Q) :=
  (TensorProduct.map T Q.mkQ).comp (splitPolynomialEquiv (K := K) h n).symm.toLinearMap

@[simp] theorem splitPolynomialDetector_apply {h n : ℕ} (T : Poly K h →ₗ[K] X)
    (Q : Submodule K (Poly K n)) (a : Poly K h) (b : Poly K n) :
    splitPolynomialDetector T Q (rename (Fin.castAdd n) a * rename (Fin.natAdd h) b) =
      T a ⊗ₜ[K] Q.mkQ b := by
  rw [← splitPolynomialEquiv_tmul]
  simp only [splitPolynomialDetector,LinearMap.comp_apply,LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply,AlgEquiv.symm_apply_apply,TensorProduct.map_tmul]

end Froberg
