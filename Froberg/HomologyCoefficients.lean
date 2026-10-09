module

public import Froberg.CoefficientExtraction

@[expose] public section

/-! The coefficient injection (C.23), on the actual Koszul homology modulo
its naturally retained old classes. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {n d r t : ℕ}

/-- The formal representative of an actual Koszul homology class. -/
def homologyFormalRepresentative (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    EndpointHomology q →ₗ[K] SymmetricSquare K (Forms K n d) :=
  ((formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
    formalMixed (Submodule.span K (Set.range q))).subtype.comp
      (endpointHomologyEquivFormal_anyChar q hq).toLinearMap

/-- The naturally included homology supported on the old generator subspace. -/
def retainedHomology (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) : Submodule K (EndpointHomology q) :=
  (formalMixed W).comap (homologyFormalRepresentative q hq)

/-- The kernel computation uses genuine polynomial multiplication and the
separation of the new symmetric products from all old products. -/
theorem homology_coefficient_kernel (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hspan : Submodule.span K (Set.range q) = W ⊔ Submodule.span K (Set.range f))
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map formalPolynomialMultiplication).comap
        (formalPolynomialMultiplication (K := K) (n := n) (d := d)) = ⊥) :
    ((relationCoefficientMap (W ⊔ Submodule.span K (Set.range f)) dual).comp
      (homologyFormalRepresentative q hq)).ker = retainedHomology q hq W := by
  ext x
  have hx : homologyFormalRepresentative q hq x ∈
      (formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
        formalMixed (W ⊔ Submodule.span K (Set.range f)) := by
    rw [← hspan]
    exact (endpointHomologyEquivFormal_anyChar q hq x).property
  constructor
  · intro h
    have hmem : homologyFormalRepresentative q hq x ∈
        (relationCoefficientMap (W ⊔ Submodule.span K (Set.range f)) dual).ker ⊓
          ((formalPolynomialMultiplication (K := K) (n := n) (d := d)).ker ⊓
            formalMixed (W ⊔ Submodule.span K (Set.range f))) := ⟨h, hx⟩
    rw [relationCoefficientMap_exact_kernel _ W f dual hdualW hdualF hsep] at hmem
    exact hmem.2
  · intro h
    exact relationCoefficientMap_kills_old W _ le_sup_left dual hdualW h

/-- Separation gives an injection of the new part of actual endpoint homology
into the array of new-generator coefficients modulo all degree-`d` relations. -/
theorem exists_injective_homology_coefficients (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hspan : Submodule.span K (Set.range q) = W ⊔ Submodule.span K (Set.range f))
    (hf : LinearIndependent K (fun i => W.mkQ (f i)))
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map formalPolynomialMultiplication).comap
        (formalPolynomialMultiplication (K := K) (n := n) (d := d)) = ⊥) :
    ∃ T : (EndpointHomology q ⧸ retainedHomology q hq W) →ₗ[K]
      (Fin t → Forms K n d ⧸ (W ⊔ Submodule.span K (Set.range f))),
      Function.Injective T := by
  obtain ⟨dual, hdualW, hdualF⟩ := exists_relative_coordinate_functionals W f hf
  let c := (relationCoefficientMap (W ⊔ Submodule.span K (Set.range f)) dual).comp
    (homologyFormalRepresentative q hq)
  have hc : c.ker = retainedHomology q hq W :=
    homology_coefficient_kernel q hq W f hspan dual hdualW hdualF hsep
  let T := (retainedHomology q hq W).liftQ c hc.ge
  refine ⟨T, LinearMap.ker_eq_bot.mp ?_⟩
  exact Submodule.ker_liftQ_eq_bot _ _ _ hc.le

/-- The extracted coefficients agree with reduction of the coefficients of a
new-generator expression, including its actual old-generator contribution. -/
theorem homology_coefficient_formula (G W : Submodule K (Forms K n d)) (hWG : W ≤ G)
    (f : Fin t → Forms K n d) (hfG : ∀ i, f i ∈ G)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0)
    (w : SymmetricSquare K (Forms K n d)) (hw : w ∈ formalMixed W)
    (a : Fin t → Forms K n d) :
    relationCoefficientMap G dual (w + formalCoefficientMap f a) = fun i => G.mkQ (a i) := by
  rw [map_add, show relationCoefficientMap G dual w = 0 from
    relationCoefficientMap_kills_old W G hWG dual hdualW hw, zero_add]
  exact relationCoefficientMap_coefficients G f hfG dual hdualF a

end Froberg
