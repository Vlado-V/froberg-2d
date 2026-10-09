module

public import Quartic.PolynomialRank
public import Quartic.PencilFibers

@[expose] public section

/-!
# The symmetric contraction bound for the convolution inverse system

If every evaluated symmetric contraction lies in a fixed two-component space
`P`, the source dimension is at most `choose (dim(P)/2+1) 2`. This proves the
linear algebra estimate behind `cv:linear-image`. Identifying the actual
convolution dual with this model remains a separate obligation.
-/

noncomputable section

namespace Quartic.ContractionBound

open Module Filter Polynomial SymmetricEvaluation

variable {K U V : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

def varyingEvaluation (H : U →ₗ[K] (V →ₗ[K] V →ₗ[K] K)) :
    V →ₗ[K] (U →ₗ[K] (V →ₗ[K] K)) where
  toFun x := evaluation H x
  map_add' x y := by
    apply LinearMap.ext
    intro u
    exact (H u).map_add x y
  map_smul' c x := by
    apply LinearMap.ext
    intro u
    exact (H u).map_smul c x

variable [Infinite K] [FiniteDimensional K U] {p : ℕ}

theorem evaluated_rank_bound
    (H : U →ₗ[K] ((Fin p → K) →ₗ[K] (Fin p → K) →ₗ[K] K))
    (P : Submodule K (((Fin p → K) →ₗ[K] K) × ((Fin p → K) →ₗ[K] K)))
    (hcontract : ∀ u t, (H u (RationalCurve.point p t),
      t • H u (RationalCurve.point p t)) ∈ P) (t₀ : K) :
    finrank K (LinearMap.range (evaluation H (RationalCurve.point p t₀))) ≤
      finrank K P / 2 := by
  have hlarge := PolynomialRank.rank_eventually_ge (varyingEvaluation H)
    (fun i : Fin p => (X : K[X]) ^ i.val) t₀
  change ∀ᶠ t in cofinite,
    finrank K (LinearMap.range (evaluation H (fun i : Fin p => ((X : K[X]) ^ i.val).eval t₀))) ≤
      finrank K (LinearMap.range (evaluation H (fun i : Fin p => ((X : K[X]) ^ i.val).eval t))) at hlarge
  have heval (t : K) : (fun i : Fin p => ((X : K[X]) ^ i.val).eval t) =
      RationalCurve.point p t := by
    funext i
    simp only [Polynomial.eval_pow, Polynomial.eval_X, RationalCurve.point]
  have hrange (t : K) :
      LinearMap.range (evaluation H (RationalCurve.point p t)) ≤ PencilFibers.fiber P t := by
    rintro _ ⟨u, rfl⟩
    exact hcontract u t
  have hfiber : ∀ᶠ t in cofinite,
      finrank K (LinearMap.range (evaluation H (RationalCurve.point p t₀))) ≤
        finrank K (PencilFibers.fiber P t) := by
    filter_upwards [hlarge] with t ht
    have ht' : finrank K (LinearMap.range (evaluation H (RationalCurve.point p t₀))) ≤
        finrank K (LinearMap.range (evaluation H (RationalCurve.point p t))) := by
      rw [← heval t₀, ← heval t]
      exact ht
    exact ht'.trans (Submodule.finrank_mono (hrange t))
  obtain ⟨s, hs⟩ := hfiber.exists
  obtain ⟨t, ht, hts⟩ := (hfiber.and (eventually_cofinite_ne s)).exists
  exact PencilFibers.equal_fiber_bound P s t (Ne.symm hts) _ hs ht

/-- The sharp binomial bound for an injective symmetric family of contractions. -/
theorem dimension_bound
    (H : U →ₗ[K] ((Fin p → K) →ₗ[K] (Fin p → K) →ₗ[K] K))
    (hH : Function.Injective H) (hsym : ∀ u x y, H u x y = H u y x)
    (P : Submodule K (((Fin p → K) →ₗ[K] K) × ((Fin p → K) →ₗ[K] K)))
    (hcontract : ∀ u t, (H u (RationalCurve.point p t),
      t • H u (RationalCurve.point p t)) ∈ P) :
    finrank K U ≤ (finrank K P / 2 + 1).choose 2 :=
  RationalCurve.symmetric_dimension_bound p H hH hsym (finrank K P / 2)
    (Filter.Eventually.of_forall (evaluated_rank_bound H P hcontract))

/-- Once the inverse-system and annihilator dimensions are identified with this
model, the preceding theorem gives exactly the manuscript's sharp shadow bound.
The two dimension identifications are explicit hypotheses. -/
theorem shadow_bound_of_model
    (H : U →ₗ[K] ((Fin p → K) →ₗ[K] (Fin p → K) →ₗ[K] K))
    (hH : Function.Injective H) (hsym : ∀ u x y, H u x y = H u y x)
    (P : Submodule K (((Fin p → K) →ₗ[K] K) × ((Fin p → K) →ₗ[K] K)))
    (hcontract : ∀ u t, (H u (RationalCurve.point p t),
      t • H u (RationalCurve.point p t)) ∈ P)
    (i imageDimension : ℕ) (hi : i ≤ 2 * p)
    (hP : finrank K P = 2 * p - i)
    (himage : imageDimension + finrank K U = (p + 1).choose 2) :
    (p + 1).choose 2 - (p - (i + 1) / 2 + 1).choose 2 ≤ imageDimension := by
  have h := dimension_bound H hH hsym P hcontract
  rw [hP] at h
  have hfloor : (2 * p - i) / 2 = p - (i + 1) / 2 := by omega
  rw [hfloor] at h
  omega

end Quartic.ContractionBound
