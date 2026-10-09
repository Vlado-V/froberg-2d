module

public import Quartic.MarkedSquareOmega
public import Quartic.AugmentedGenericOmega

@[expose] public section

/-! A fixed actual mixed square can be retained on the same coefficient
space as the preceding middle and trace conditions. -/
noncomputable section
namespace Quartic.MarkedSquareGenericOmega
open Module MvPolynomial HomologyCoordinates AugmentedMiddle AugmentedGeneric
open AugmentedGenericOmega MarkedSquareEmbedding
variable {K : Type*} [Field K] {m c q : ℕ}
set_option maxHeartbeats 1200000

def productWithSquare (g : Fin c → MiddleCoordinates.Mixed K m)
    (ζ : MiddleCoordinates.Mixed K m) :
    (Forms K c 2 × K) →ₗ[K] (Forms K m 2 × Forms K m 2) :=
  (productMap g).coprod (LinearMap.toSpanSingleton K _
    (MiddleCoordinates.projectedProduct ζ ζ))

@[simp] theorem productWithSquare_apply (g : Fin c → MiddleCoordinates.Mixed K m)
    (ζ : MiddleCoordinates.Mixed K m) (b : Forms K c 2) (a : K) :
    productWithSquare g ζ (b,a) = productMap g b + a • MiddleCoordinates.projectedProduct ζ ζ := rfl

theorem productWithSquare_specialization (hc : c < m) :
    productWithSquare (mixedFamily (K := K) hc.le) (zeta hc) = (embedding hc).prod 0 := by
  apply LinearMap.ext
  rintro ⟨b,a⟩
  rw [productWithSquare_apply, productMap_specialization, zeta_product]
  apply Prod.ext <;> simp [embedding]

theorem productWithSquare_polynomial {ι : Type*}
    (g : (ι → K) → (Fin c → MiddleCoordinates.Mixed K m))
    (hg : ∀ i, IsPolynomialFamily (fun a => g a i)) (ζ : MiddleCoordinates.Mixed K m) :
    IsPolynomialFamily (fun a => productWithSquare (g a) ζ) := by
  apply isPolynomialFamily_linearMap
  rintro ⟨b,t⟩
  exact ((productMap_polynomial g hg).linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Forms K m 2 × Forms K m 2) b)).add
      (isPolynomialFamily_const (t • MiddleCoordinates.projectedProduct ζ ζ))

abbrev LiftedSource (K : Type*) [Field K] (m c q : ℕ) :=
  (((Forms K c 2 × K) × (Forms K m 2 × BlockHomology K)) × (Fin q → K))

def liftedFamily (ω : K) (ζ : MiddleCoordinates.Mixed K m) (a : ParameterIndex m c q → K) :
    LiftedSource K m c q →ₗ[K] (Forms K m 2 × Forms K m 2) :=
  AugmentedGenericOmega.lifted ω (productWithSquare (coefficientMixed a) ζ)
    (coefficientChild a) (coefficientMotions a)

theorem liftedFamily_polynomial (ω : K) (ζ : MiddleCoordinates.Mixed K m) :
    IsPolynomialFamily (liftedFamily (K := K) (c := c) (q := q) ω ζ) := by
  apply AugmentedGenericOmega.lifted_polynomial ω
  · apply productWithSquare_polynomial
    intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMixed)
  · intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientChild)
  · intro i
    exact isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMotions)

theorem exists_injective_parameter (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hc : c < m) (hbudget : q + (c + 1).choose 2 + 4 ≤ (m + 1).choose 2) :
    ∃ a : ParameterIndex m c q → K,
      LinearIndependent K (coefficientMixed a) ∧ LinearIndependent K (coefficientChild a) ∧
      Function.Injective (liftedFamily ω (zeta hc) a) := by
  obtain ⟨hg, _, Q, hQ, _, r, _, hr, _⟩ :=
    MarkedSquareOmega.marked_augmented_witness ω hω hω1 hc hbudget
  obtain ⟨h, hh, hspan⟩ := MiddleGeneric.family_of_submodule Q hQ
  let r₀ : Fin 4 → Forms K m 2 := fun i => Classical.choose (Q.mkQ_surjective (r i))
  have hr₀ : (fun i => Q.mkQ (r₀ i)) = r :=
    funext (fun i => Classical.choose_spec (Q.mkQ_surjective (r i)))
  have hquot : Function.Injective (AugmentedGenericOmega.quotientAugmented ω
      (productWithSquare (mixedFamily hc.le) (zeta hc)) h r₀) := by
    apply (AugmentedGenericOmega.quotientAugmented_span_eq ω _ h r₀ Q hspan).mpr
    rw [productWithSquare_specialization, hr₀]
    exact hr
  refine ⟨encode (mixedFamily hc.le) h r₀, ?_, ?_, ?_⟩
  · simpa only [coefficientMixed_encode] using hg
  · simpa only [coefficientChild_encode] using hh
  · simpa only [liftedFamily, coefficientMixed_encode, coefficientChild_encode,
      coefficientMotions_encode] using AugmentedGenericOmega.lifted_injective_of_quotient ω
      (productWithSquare (mixedFamily hc.le) (zeta hc)) h r₀ hh hquot

def GenericMarkedAugmented (ω : K) (ζ : MiddleCoordinates.Mixed K m) (c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex m c q) K, (∃ a₀, eval a₀ D ≠ 0) ∧
    ∀ a, eval a D ≠ 0 → LinearIndependent K (coefficientMixed a) ∧
      LinearIndependent K (coefficientChild a) ∧ Function.Injective
        (AugmentedGenericOmega.quotientAugmented ω
          (productWithSquare (coefficientMixed a) ζ) (coefficientChild a) (coefficientMotions a))

/-- The D.12 open uses exactly the old mixed/child/pure-motion parameter space. -/
theorem genericMarkedAugmented_of_budget (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1)
    (hc : c < m) (hbudget : q + (c + 1).choose 2 + 4 ≤ (m + 1).choose 2) :
    GenericMarkedAugmented ω (zeta hc) c q := by
  classical
  obtain ⟨a₀, hg, hh, hi⟩ := exists_injective_parameter ω hω hω1 hc hbudget
  obtain ⟨Dg, hDg, hpg⟩ := independent_polynomial_principal_open
    (fun i a => coefficientMixed (K := K) (m := m) (c := c) (q := q) a i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientMixed)) a₀ hg
  obtain ⟨Dh, hDh, hph⟩ := independent_polynomial_principal_open
    (fun i a => coefficientChild (K := K) (m := m) (c := c) (q := q) a i)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp coefficientChild)) a₀ hh
  obtain ⟨Dl, hDl, hpl⟩ := injective_polynomial_principal_open
    (liftedFamily (K := K) (c := c) (q := q) ω (zeta hc))
    (liftedFamily_polynomial ω (zeta hc)) a₀ hi
  refine ⟨Dg * Dh * Dl, ⟨a₀, ?_⟩, ?_⟩
  · simpa only [map_mul] using mul_ne_zero (mul_ne_zero hDg hDh) hDl
  · intro a ha
    simp only [map_mul, mul_ne_zero_iff] at ha
    exact ⟨hpg a ha.1.1, hph a ha.1.2,
      AugmentedGenericOmega.quotient_injective_of_lifted ω _ _ _ (hpl a ha.2)⟩

end Quartic.MarkedSquareGenericOmega
