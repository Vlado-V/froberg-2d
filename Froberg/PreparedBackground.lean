import Froberg.LowHomogeneousProduct
import Froberg.FormalHomology

/-! Exact low-X-degree conditions on an actual prepared background. The
record does not assume the desired product separation: it controls only
three components of each generator, and the product conclusion is proved. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K : Type} [Field K] {h m d : ℕ}

/-- X variables have weight one, Y variables weight zero. -/
def coreWeight (h m : ℕ) : Fin (h+m) → ℕ := Fin.addCases (fun _ => 1) (fun _ => 0)

/-- Exact X-degree projection on the actual ambient polynomial ring. -/
def coreComponent (h m i : ℕ) : Poly K (h+m) →ₗ[K] Poly K (h+m) :=
  weightedHomogeneousComponent (coreWeight h m) i

/-- The actual coefficient forms of total degree d and a fixed X-degree. -/
def coreCoefficientSpace (K : Type) [Field K] (h m d i : ℕ) : Submodule K (Poly K (h+m)) :=
  (Forms K (h+m) d).map (coreComponent h m i)

/-- Conditions satisfied by the scalar, private linear, and quadratic pieces
of each actual background generator. Higher components are unrestricted. -/
structure PreparedLowComponents (W : Submodule K (Forms K (h+m) d))
    (S P D : Submodule K (Poly K (h+m))) : Prop where
  scalar : ∀ w : Forms K (h+m) d, w ∈ W → coreComponent h m 0 w.val ∈ S
  linear : ∀ w : Forms K (h+m) d, w ∈ W → coreComponent h m 1 w.val ∈ P
  quadratic : ∀ w : Forms K (h+m) d, w ∈ W → coreComponent h m 2 w.val ∈ D

/-- The three denominator pieces seen by quadratic-X-degree extraction. -/
def preparedProductDenominator (S P D : Submodule K (Poly K (h+m))) :
    Submodule K (Poly K (h+m)) :=
  S*coreCoefficientSpace K h m d 2 ⊔
    P*coreCoefficientSpace K h m d 1 ⊔ D*coreCoefficientSpace K h m d 0

/-- Every old product has its X-degree-two component in the explicit scalar,
private, and quadratic denominator. No higher component contributes. -/
theorem prepared_product_component_mem
    (W : Submodule K (Forms K (h+m) d)) (S P D : Submodule K (Poly K (h+m)))
    (H : PreparedLowComponents W S P D) (w : Forms K (h+m) d) (hw : w ∈ W)
    (a : Forms K (h+m) d) :
    coreComponent h m 2 (w.val*a.val) ∈ preparedProductDenominator (d := d) S P D := by
  have ha (i : ℕ) : coreComponent h m i a.val ∈ coreCoefficientSpace K h m d i :=
    ⟨a.val,a.property,rfl⟩
  have h0 := Submodule.mul_mem_mul (H.scalar w hw) (ha 2)
  have h1 := Submodule.mul_mem_mul (H.linear w hw) (ha 1)
  have h2 := Submodule.mul_mem_mul (H.quadratic w hw) (ha 0)
  change weightedHomogeneousComponent (coreWeight h m) 2 (w.val*a.val) ∈ _
  rw [weightedHomogeneousComponent_two_product]
  unfold preparedProductDenominator
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left h0)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right h1)
  · exact Submodule.mem_sup_right h2

/-- A detector supported in X-degree two kills all old products once it kills
the three explicit denominator pieces. This feeds the actual C.2 theorem. -/
theorem prepared_background_annihilated {X : Type*} [AddCommGroup X] [Module K X]
    (W : Submodule K (Forms K (h+m) d)) (S P D : Submodule K (Poly K (h+m)))
    (H : PreparedLowComponents W S P D) (T : Poly K (h+m) →ₗ[K] X)
    (hT : T.comp (coreComponent h m 2) = T)
    (hdenom : preparedProductDenominator (d := d) S P D ≤ T.ker) :
    ∀ w : Forms K (h+m) d, w ∈ W → ∀ a : Forms K (h+m) d, T (w.val*a.val) = 0 := by
  intro w hw a
  have he := LinearMap.congr_fun hT (w.val*a.val)
  exact he.symm.trans (hdenom (prepared_product_component_mem W S P D H w hw a))

/-- The formal mixed-product image is also annihilated, without any assertion
of independence or exactness hidden in the background record. -/
theorem prepared_formalMixed_map_le_ker {X : Type*} [AddCommGroup X] [Module K X]
    (W : Submodule K (Forms K (h+m) d)) (S P D : Submodule K (Poly K (h+m)))
    (H : PreparedLowComponents W S P D) (T : Poly K (h+m) →ₗ[K] X)
    (hT : T.comp (coreComponent h m 2) = T)
    (hdenom : preparedProductDenominator (d := d) S P D ≤ T.ker) :
    (formalMixed W).map formalPolynomialMultiplication ≤
      (T.comp (Forms K (h+m) (2*d)).subtype).ker := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨a,b,ha,rfl⟩
  change T ((formalPolynomialMultiplication (symProd a b)).val) = 0
  rw [formalPolynomialMultiplication_symProd]
  exact prepared_background_annihilated W S P D H T hT hdenom a ha b

end Froberg
