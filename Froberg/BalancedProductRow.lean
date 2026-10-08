import Froberg.FiniteProductRow
import Froberg.BalancedScalarCoordinates
import Froberg.ProductRowRename

/-! Product-row witnesses in the scalar coordinates used by the quotient estimates. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X]

/-- Changing only scalar coordinates commutes with every output detector. -/
theorem biformOutputMap_rename_scalar {σ τ υ : Type*}
    (T : MvPolynomial σ K →ₗ[K] X) (f : τ → υ)
    (p : MvPolynomial (σ ⊕ τ) K) :
    biformOutputMap T (rename (Sum.map id f) p)=
      TensorProduct.map LinearMap.id (rename f).toLinearMap (biformOutputMap T p) := by
  obtain ⟨z,rfl⟩ := (MvPolynomial.tensorEquivSum K σ τ K).surjective p
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [tensorEquivSum_tmul,map_mul,rename_rename,rename_rename]
    have hleft : (Sum.map (id : σ → σ) f) ∘ Sum.inl=(Sum.inl : σ → σ ⊕ υ) := rfl
    have hright : (Sum.map (id : σ → σ) f) ∘ Sum.inr=(Sum.inr : υ → σ ⊕ υ) ∘ f := rfl
    rw [hleft,hright,← rename_rename,biformOutputMap_tmul,biformOutputMap_tmul]
    rfl
  | add a b ha hb => simp only [map_add,ha,hb]

namespace ProductRows
variable [Module.Finite K X]

/-- The constrained finite construction retains all four degree conditions
and its exact output constraint after using a balanced finite scalar set. -/
theorem exists_balanced_product_row {w v d R : ℕ} (hw : 0<w) (hv : 0<v)
    (J : Finset ℕ) (e : ℕ → ℕ)
    (heven : ∀ j∈J,Even j) (hdegree : ∀ j∈J,j≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hdiag : ∀ r : Row J R,r.val.val=R-r.val.val →
      e r.val.val≤(w.choose r.val.val-finrank K X)*(v.choose (d-r.val.val)/2))
    (hcross : ∀ r : Row J R,r.val.val≠R-r.val.val →
      e r.val.val≤((w+r.val.val-1).choose r.val.val-finrank K X)*(v+(d-r.val.val)-1).choose (d-r.val.val) ∧
      e (R-r.val.val)≤((w+(R-r.val.val)-1).choose (R-r.val.val)-finrank K X)*
        (v+(d-(R-r.val.val))-1).choose (d-(R-r.val.val))) :
    ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial ((Fin w × Bool) ⊕ Fin (v+v)) K,
      (∀ j i,(q j i).IsHomogeneous d ∧
        (q j i).IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) j ∧
        (q j i).IsWeightedHomogeneous (Sum.elim pairedHalfWeight (fun _ => 0)) (assignedDegree R j) ∧
        (q j i).IsWeightedHomogeneous
          (Sum.elim (fun _ => 0) (halfWeight (balancedScalarHalf v))) (assignedScalarDegree R d j) ∧
        biformOutputMap (T j) (q j i)=0) ∧
      Function.Injective (multiplication e q J R) := by
  obtain ⟨q,hq,hi⟩ := exists_constrained_product_row hw hv J e heven hdegree T hdiag hcross
  let f := (Equiv.refl (Fin w × Bool)).sumCongr (pairedScalarEquiv v)
  refine ⟨fun j i => rename f (q j i),?_,multiplication_rename_injective e q f.toEmbedding J R hi⟩
  intro j i
  refine ⟨(hq j i).1.rename_isHomogeneous,?_,?_,?_,?_⟩
  · apply rename_weightedHomogeneous f.toEmbedding FourBlocks.outputWeight _ _ (hq j i).2.1
    rintro (a|b) <;> rfl
  · exact fourBlock_output_weight_transport (hq j i).2.2.1
  · exact fourBlock_scalar_weight_transport (hq j i).2.2.2.1
  · change biformOutputMap (T j) (rename (Sum.map id (pairedScalarEquiv v)) (q j i))=0
    rw [biformOutputMap_rename_scalar,(hq j i).2.2.2.2,map_zero]

end ProductRows
end Froberg
