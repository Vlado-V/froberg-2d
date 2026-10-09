module

public import Froberg.HomologyCoefficientMotion
public import Froberg.ProjectedDeformation

@[expose] public section

/-! Faithful new-generator coefficients and their actual normal-motion
formula after any fixed projection of the endpoint target. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
namespace Froberg
open Module
variable {K : Type} [Field K]
variable {Z : Type*} [AddCommGroup Z] [Module K Z]
variable {n d r t : ℕ}

/-- Actual projected cycles still have canonical formal representatives. -/
def projectedCycleToFormal (pi : Forms K n (2*d) →ₗ[K] Z)
    (q : Fin r → Forms K n d) :
    (projectedEndpointMultiplication pi q).ker →ₗ[K] SymmetricSquare K (Forms K n d) :=
  (formalCoefficientMap q).comp (projectedEndpointMultiplication pi q).ker.subtype

theorem projectedCycleToFormal_kernel (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    (projectedCycleToFormal pi q).ker =
      kernelBoundary (projectedEndpointMultiplication pi q) (koszulSpace q) := by
  change (formalCoefficientMap q).ker.comap (projectedEndpointMultiplication pi q).ker.subtype = _
  rw [ker_formalCoefficientMap_anyChar q hq]
  rfl

/-- The projected analogue of the formal representative map, constructed by
an actual quotient lift rather than an assumed identification. -/
def projectedFormalRepresentative (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    ProjectedEndpointHomology pi q →ₗ[K] SymmetricSquare K (Forms K n d) :=
  (projectedCycleToFormal pi q).range.subtype.comp
    (kernelModuloEquivRange (Z := SymmetricSquare K (Forms K n d))
      (projectedEndpointMultiplication pi q) (koszulSpace q)
      (projectedCycleToFormal pi q) (projectedCycleToFormal_kernel pi q hq)).toLinearMap

@[simp] theorem projectedFormalRepresentative_mk (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (a : (projectedEndpointMultiplication pi q).ker) :
    projectedFormalRepresentative pi q hq
      (kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q) a) =
      formalCoefficientMap q a.val := rfl

theorem projectedFormalRepresentative_mem (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (x : ProjectedEndpointHomology pi q) :
    projectedFormalRepresentative pi q hq x ∈
      (pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed (Submodule.span K (Set.range q)) := by
  obtain ⟨a,rfl⟩ := kernelClass_surjective (projectedEndpointMultiplication pi q) (koszulSpace q) x
  rw [projectedFormalRepresentative_mk]
  constructor
  · change pi (formalPolynomialMultiplication (formalCoefficientMap q a.val)) = 0
    have hf := LinearMap.congr_fun (formalPolynomialMultiplication_comp q) a.val
    change formalPolynomialMultiplication (formalCoefficientMap q a.val) = endpointMultiplication q a.val at hf
    rw [hf]
    exact a.property
  · rw [← range_formalCoefficientMap q]
    exact ⟨a.val,rfl⟩

/-- The projected representative loses exactly the constant Koszul boundary. -/
theorem projectedFormalRepresentative_injective (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    Function.Injective (projectedFormalRepresentative pi q hq) := by
  intro x y hxy
  let e := kernelModuloEquivRange (Z := SymmetricSquare K (Forms K n d))
    (projectedEndpointMultiplication pi q) (koszulSpace q)
    (projectedCycleToFormal pi q) (projectedCycleToFormal_kernel pi q hq)
  apply e.injective
  apply Subtype.ext
  exact hxy

/-- Every projected formal relation comes from an actual projected cycle. -/
theorem projectedFormalRepresentative_range (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    (projectedFormalRepresentative pi q hq).range =
      (pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed (Submodule.span K (Set.range q)) := by
  ext x
  constructor
  · rintro ⟨x,rfl⟩
    exact projectedFormalRepresentative_mem pi q hq x
  · rintro ⟨hx,hmem⟩
    rw [← range_formalCoefficientMap q] at hmem
    obtain ⟨a,rfl⟩ := hmem
    have ha : projectedEndpointMultiplication pi q a = 0 := by
      change pi (endpointMultiplication q a) = 0
      rw [← formalPolynomialMultiplication_comp q]
      exact hx
    refine ⟨kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q) ⟨a,ha⟩,?_⟩
    exact projectedFormalRepresentative_mk pi q hq ⟨a,ha⟩

/-- Actual projected homology is exactly the projected formal-product kernel. -/
def projectedHomologyEquivFormal (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    ProjectedEndpointHomology pi q ≃ₗ[K]
      ((pi.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range q)) : Submodule K (SymmetricSquare K (Forms K n d))) :=
  (LinearEquiv.ofInjective (projectedFormalRepresentative pi q hq)
    (projectedFormalRepresentative_injective pi q hq)).trans
      (LinearEquiv.ofEq _ _ (projectedFormalRepresentative_range pi q hq))

def projectedRetainedHomology (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) : Submodule K (ProjectedEndpointHomology pi q) :=
  (formalMixed W).comap (projectedFormalRepresentative pi q hq)

def projectedHomologyCoefficients (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (G : Submodule K (Forms K n d)) (dual : Fin t → Forms K n d →ₗ[K] K) :
    ProjectedEndpointHomology pi q →ₗ[K] (Fin t → Forms K n d ⧸ G) :=
  (relationCoefficientMap G dual).comp (projectedFormalRepresentative pi q hq)

@[simp] theorem projectedHomologyCoefficients_mk (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (G : Submodule K (Forms K n d)) (hqG : ∀ j, q j ∈ G)
    (dual : Fin t → Forms K n d →ₗ[K] K) (a : (projectedEndpointMultiplication pi q).ker) :
    projectedHomologyCoefficients pi q hq G dual
      (kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q) a) =
      fun i => ∑ j, dual i (q j) • G.mkQ (a.val j) := by
  rw [projectedHomologyCoefficients,LinearMap.comp_apply,projectedFormalRepresentative_mk]
  exact relationCoefficientMap_general_coefficients G q hqG dual a.val

/-- C.2 separation for the projected target proves the exact retained kernel. -/
theorem projectedHomologyCoefficients_kernel (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hspan : Submodule.span K (Set.range q) = W ⊔ Submodule.span K (Set.range f))
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map (pi.comp formalPolynomialMultiplication)).comap
        (pi.comp (formalPolynomialMultiplication (K := K) (n := n) (d := d))) = ⊥) :
    (projectedHomologyCoefficients pi q hq (W ⊔ Submodule.span K (Set.range f)) dual).ker =
      projectedRetainedHomology pi q hq W := by
  ext x
  have hx := projectedFormalRepresentative_mem pi q hq x
  rw [hspan] at hx
  constructor
  · intro h
    have hh : projectedFormalRepresentative pi q hq x ∈
        (relationCoefficientMap (W ⊔ Submodule.span K (Set.range f)) dual).ker ⊓
          ((pi.comp formalPolynomialMultiplication).ker ⊓
            formalMixed (W ⊔ Submodule.span K (Set.range f))) := ⟨h,hx⟩
    rw [relationCoefficientMap_exact_kernel _ W f dual hdualW hdualF hsep] at hh
    exact hh.2
  · intro h
    exact relationCoefficientMap_kills_old W _ le_sup_left dual hdualW h

/-- The projected faithful coefficient map retains its defining formula. -/
theorem exists_injective_projected_coefficients (pi : Forms K n (2*d) →ₗ[K] Z) (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (W : Submodule K (Forms K n d)) (f : Fin t → Forms K n d)
    (hspan : Submodule.span K (Set.range q) = W ⊔ Submodule.span K (Set.range f))
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (hdualW : ∀ i w, w ∈ W → dual i w = 0)
    (hdualF : ∀ i j, dual i (f j) = if i = j then 1 else 0)
    (hsep : formalSquare (Submodule.span K (Set.range f)) ⊓
      ((formalMixed W).map (pi.comp formalPolynomialMultiplication)).comap
        (pi.comp (formalPolynomialMultiplication (K := K) (n := n) (d := d))) = ⊥) :
    ∃ E : (ProjectedEndpointHomology pi q ⧸ projectedRetainedHomology pi q hq W) →ₗ[K]
        (Fin t → Forms K n d ⧸ (W ⊔ Submodule.span K (Set.range f))),
      Function.Injective E ∧ E.comp (projectedRetainedHomology pi q hq W).mkQ =
        projectedHomologyCoefficients pi q hq (W ⊔ Submodule.span K (Set.range f)) dual := by
  have hc := projectedHomologyCoefficients_kernel pi q hq W f hspan dual hdualW hdualF hsep
  let E := (projectedRetainedHomology pi q hq W).liftQ
    (projectedHomologyCoefficients pi q hq (W ⊔ Submodule.span K (Set.range f)) dual) hc.ge
  refine ⟨E,LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hc.le),?_⟩
  ext x
  rfl

/-- Literal compatibility with the first normal map after target deletion. -/
theorem projectedNormalMap_coefficient_formula [Infinite K] [FiniteDimensional K Z]
    {J : Type*} [AddCommGroup J] [Module K J]
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (G : Submodule K (Forms K n d)) (hqG : ∀ j, q j ∈ G)
    (dual : Fin t → Forms K n d →ₗ[K] K)
    (mu : Forms K n d →ₗ[K] (Forms K n d ⧸ G) →ₗ[K] J)
    (rho : ProjectedEndpointCokernel pi q →ₗ[K] J)
    (hmu : ∀ z a, mu z (G.mkQ a) =
      rho (cokernelClass (projectedEndpointMultiplication pi q) (pi (mulForm z a))))
    (z : Fin t → Forms K n d) :
    rho.comp (projectedNormalMap pi q (relativeGeneratorMotion q dual z)) =
      (coefficientResponse G mu z).comp (projectedHomologyCoefficients pi q hq G dual) := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,rfl⟩ := kernelClass_surjective (projectedEndpointMultiplication pi q) (koszulSpace q) x
  rw [LinearMap.comp_apply,LinearMap.comp_apply,projectedHomologyCoefficients_mk pi q hq G hqG]
  rw [coefficientResponse_apply]
  change rho (cokernelClass (projectedEndpointMultiplication pi q)
    (pi (endpointMultiplication (relativeGeneratorMotion q dual z) a.val))) = _
  have hp : endpointMultiplication (relativeGeneratorMotion q dual z) a.val =
      ∑ j, ∑ i, dual i (q j) • mulForm (z i) (a.val j) := by
    apply Subtype.ext
    simp [endpointMultiplication_val,relativeGeneratorMotion,Finset.sum_mul,mulForm]
  rw [hp]
  simp only [map_sum,map_smul,hmu]
  rw [Finset.sum_comm]

end Froberg
