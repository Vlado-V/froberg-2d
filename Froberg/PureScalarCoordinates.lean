import Froberg.BiformCoordinates

/-! Output-weight zero is precisely the embedded scalar polynomial space. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d : ℕ}

/-- Every zero-output biform is the rename of a homogeneous scalar form. -/
theorem biform_zero_output_exists {f : MvPolynomial (σ ⊕ Fin n) K}
    (hf : f∈biformImage (homogeneousSubmodule σ K 0) (Forms K n d)) :
    ∃ b : Forms K n d,rename Sum.inr b.val=f := by
  rcases hf with ⟨a,⟨z,rfl⟩,rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have ha : a.val=C (a.val.coeff 0) := by
      simpa only [homogeneousComponent_zero] using (homogeneousComponent_eq_self a.property).symm
    refine ⟨(a.val.coeff 0) • b,?_⟩
    change rename Sum.inr ((a.val.coeff 0) • b.val)=
      tensorEquivSum K σ (Fin n) K (a.val ⊗ₜ[K] b.val)
    rw [tensorEquivSum_tmul,ha,rename_C]
    simp only [map_smul,MvPolynomial.C_mul']
    simp
  | add z z' hz hz' =>
    obtain ⟨b,hb⟩ := hz
    obtain ⟨b',hb'⟩ := hz'
    refine ⟨b+b',?_⟩
    simpa only [Submodule.coe_add,map_add] using congrArg₂ HAdd.hAdd hb hb'

/-- A total degree-d polynomial with output weight zero has unique scalar
coordinates; existence is enough for row elimination. -/
theorem homogeneous_output_zero_exists {f : MvPolynomial (σ ⊕ Fin n) K}
    (hf : f.IsHomogeneous d)
    (hzero : f.IsWeightedHomogeneous (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) 0) :
    ∃ b : Forms K n d,rename Sum.inr b.val=f := by
  apply biform_zero_output_exists
  apply mem_biformImage_of_homogeneous (R := 0)
  · simpa only [zero_add] using hf
  · exact hzero

end Froberg
