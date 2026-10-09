module

public import Froberg.HomogeneousNormalized
public import Froberg.Prefix
public import Froberg.IntrinsicProjection

@[expose] public section

/-! Uniform normalized growth and its generic projection, for the actual
multiplication of homogeneous forms. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic
variable {K : Type*} [Field K] {n d e : ℕ}

/-- The bilinear image of graded multiplication is the genuine polynomial
product subspace after forgetting the homogeneous subtype. -/
theorem graded_image_polynomial (L : Submodule K (Forms K n e)) :
    (BilinearImage.image (gradedMultiplication (K := K) (n := n) (d := d) (e := e)) L).map
      (Forms K n (d+e)).subtype = Forms K n d * L.map (Forms K n e).subtype := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    intro f
    rintro _ ⟨g,hg,rfl⟩
    exact Submodule.mul_mem_mul f.property ⟨g,hg,rfl⟩
  · apply Submodule.mul_le.mpr
    intro f hf g hg
    obtain ⟨g,hg,rfl⟩ := hg
    exact ⟨gradedMultiplication ⟨f,hf⟩ g,
      BilinearImage.product_mem gradedMultiplication L ⟨f,hf⟩ g hg,rfl⟩

/-- The actual graded multiplication obeys the ordinary normalized estimate
in every pair of degrees, without an asymptotic hypothesis. -/
theorem graded_normalized_growth (hn : 0 < n) (L : Submodule K (Forms K n e)) :
    finrank K (Forms K n (d+e))*finrank K L ≤
      finrank K (Forms K n e)*
        finrank K (BilinearImage.image (gradedMultiplication (K := K) (n := n) (d := d) (e := e)) L) := by
  have hL : L.map (Forms K n e).subtype ≤ Forms K n e := by
    rintro _ ⟨v,hv,rfl⟩
    exact v.property
  have h := homogeneous_normalized_growth (d := d) hn _ hL
  rw [Submodule.finrank_map_subtype_eq] at h
  have heq := congrArg (fun U : Submodule K (Poly K n) => finrank K U)
    (graded_image_polynomial (d := d) L)
  rw [Submodule.finrank_map_subtype_eq,mul_comm] at heq
  rw [← heq] at h
  simpa only [finrank_forms K n (d+e) hn,finrank_forms K n e hn,Nat.add_comm e d] using h

/-- The C.8 projection statement for actual multiplication by linear forms.
All remaining hypotheses are the explicit finite numerical dimension margin. -/
theorem exists_projected_linear_growth [Infinite K] (hn : 0 < n) {u b : ℕ}
    (hW : (n+(1+e)-1).choose (1+e)=u+b)
    (hmargin : ((n+e-1).choose e)*((n+e-1).choose e) < u*b) :
    ∃ P : Forms K n (1+e) →ₗ[K] (Fin b → K),
      Function.Surjective P ∧ finrank K P.ker=u ∧
      ∀ L : Submodule K (Forms K n e),
        b*finrank K L ≤ finrank K (Forms K n e)*
          finrank K ((BilinearImage.image (gradedMultiplication (d := 1) (e := e)) L).map P) := by
  apply exists_normalized_projection
    (show 0 < finrank K (Forms K n e) by
      rw [finrank_forms K n e hn]
      exact Nat.choose_pos (by omega))
    (by simpa only [finrank_forms K n (1+e) hn] using hW)
    (by simpa only [finrank_forms K n e hn] using hmargin)
    (gradedMultiplication (d := 1) (e := e))
  exact graded_normalized_growth hn

end Froberg
