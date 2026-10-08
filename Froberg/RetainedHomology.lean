import Froberg.HomologyCoefficients

/-! The retained formal-relation subspace is precisely the image of the
actual homology inclusion from the old generators. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K] {n d r t : ℕ}

theorem retainedHomology_eq_range (htwo : (2 : K) ≠ 0)
    (q : Fin r → Forms K n d) (f : Fin t → Forms K n d)
    (hq : LinearIndependent K q) (hf : LinearIndependent K f)
    (hspan : Submodule.span K (Set.range q) ≤ Submodule.span K (Set.range f)) :
    retainedHomology htwo f hf (Submodule.span K (Set.range q)) =
      (endpointHomologyInclusion htwo q f hq hf hspan).range := by
  let eq := endpointHomologyEquivFormal htwo q hq
  let ef := endpointHomologyEquivFormal htwo f hf
  ext x
  constructor
  · intro hx
    let y : ((formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
        formalMixed (Submodule.span K (Set.range q)) :
          Submodule K (SymmetricSquare K (Forms K n d))) :=
      ⟨(ef x).val, (ef x).property.1, hx⟩
    refine ⟨eq.symm y, ?_⟩
    apply ef.injective
    apply Subtype.ext
    change (ef (ef.symm ⟨(eq (eq.symm y)).val, _⟩)).val = (ef x).val
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨y, rfl⟩
    change (ef (ef.symm ⟨(eq y).val, _⟩)).val ∈ formalMixed (Submodule.span K (Set.range q))
    rw [LinearEquiv.apply_symm_apply]
    exact (eq y).property.2

end Froberg
