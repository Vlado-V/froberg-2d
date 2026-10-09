module

public import Froberg.ParityComplex

@[expose] public section

/-! Variable equivalences preserve the actual homogeneous parity spaces,
with the weight function transported along the same equivalence. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ τ M : Type*} [Field K] [AddCommMonoid M]

theorem weighted_homogeneous_rename (e : σ ↪ τ) (w : τ → M)
    (f : MvPolynomial σ K) (p : M) (hf : f.IsWeightedHomogeneous (w ∘ e) p) :
    (rename e f).IsWeightedHomogeneous w p := by
  classical
  intro a ha
  have ha' : a∈(rename e f).support := mem_support_iff.mpr ha
  rw [support_rename_of_injective e.injective] at ha'
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha'
  have hw : Finsupp.weight w (Finsupp.mapDomain e b)=Finsupp.weight (w ∘ e) b := by
    unfold Finsupp.weight
    simp
  rw [hw]
  exact hf (mem_support_iff.mp hb)


def homogeneousParitySpace (K : Type*) [Field K] (σ : Type*)
    (d : ℕ) (w : σ → M) (p : M) : Submodule K (MvPolynomial σ K) :=
  homogeneousSubmodule σ K d ⊓ weightedHomogeneousSubmodule K w p

def homogeneousParityRenameEquiv (e : σ ≃ τ) (w : σ → M) (d : ℕ) (p : M) :
    homogeneousParitySpace K σ d w p ≃ₗ[K]
      homogeneousParitySpace K τ d (w ∘ e.symm) p where
  toFun f := ⟨rename e f.val,⟨f.property.1.rename_isHomogeneous,by
    apply weighted_homogeneous_rename e.toEmbedding (w ∘ e.symm) f.val p
    change f.val.IsWeightedHomogeneous (fun x => w (e.symm (e x))) p
    simpa only [Equiv.symm_apply_apply] using (show f.val.IsWeightedHomogeneous w p from f.property.2)⟩⟩
  invFun f := ⟨rename e.symm f.val,⟨f.property.1.rename_isHomogeneous,by
    exact weighted_homogeneous_rename e.symm.toEmbedding w f.val p f.property.2⟩⟩
  left_inv f := by
    apply Subtype.ext
    exact (renameEquiv K e).left_inv f.val
  right_inv f := by
    apply Subtype.ext
    exact (renameEquiv K e).right_inv f.val
  map_add' f g := Subtype.ext (map_add (rename e) f.val g.val)
  map_smul' c f := Subtype.ext (map_smul (rename e) c f.val)

end Froberg
