import Froberg.PluckerCoordinates
import Froberg.PrimitiveVectors
import Froberg.PluckerLine

/-! # Primitive normalization of actual invariant Plücker coordinates -/

namespace Froberg
open Matrix Module

variable {R F J : Type*} [CommRing R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Fintype J] [DecidableEq J]

/-- Changing a nonzero scalar representative of a semilinearly invariant
line preserves its invariance, with the scalar twist accounted for. -/
theorem semilinear_proportional_normalization
    (e : R ≃+* R) (A : Matrix J J R)
    (w : J → F) (v : J → R) (c : F) (hc : c ≠ 0)
    (hw : ∀ i, w i = c * algebraMap R F (v i))
    (hline : ∃ l : F,
      A.map (algebraMap R F) *ᵥ
        (fun i => IsFractionRing.ringEquivOfRingEquiv e (w i)) = l • w) :
    ∃ l : F, ∀ i, algebraMap R F ((A *ᵥ (fun j => e (v j))) i) =
      l * algebraMap R F (v i) := by
  let E : F ≃+* F := IsFractionRing.ringEquivOfRingEquiv e
  obtain ⟨l, hl⟩ := hline
  have he : (fun i => E (w i)) = E c • (fun i => algebraMap R F (e (v i))) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, hw, map_mul]
    rw [show E (algebraMap R F (v i)) = algebraMap R F (e (v i)) from
      IsFractionRing.ringEquivOfRingEquiv_algebraMap e (v i)]
  change A.map (algebraMap R F) *ᵥ (fun i => E (w i)) = l • w at hl
  rw [he, Matrix.mulVec_smul] at hl
  have hec : E c ≠ 0 := E.map_ne_zero_iff.mpr hc
  refine ⟨(E c)⁻¹ * l * c, ?_⟩
  intro i
  have hi := congrFun hl i
  simp only [Pi.smul_apply, smul_eq_mul, hw] at hi
  have hmap : algebraMap R F ((A *ᵥ (fun j => e (v j))) i) =
      (A.map (algebraMap R F) *ᵥ (fun j => algebraMap R F (e (v j)))) i :=
    (algebraMap R F).map_mulVec A (fun j => e (v j)) i
  rw [← hmap] at hi
  calc
    algebraMap R F ((A *ᵥ (fun j => e (v j))) i) =
        (E c)⁻¹ * (E c * algebraMap R F ((A *ᵥ (fun j => e (v j))) i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hec, one_mul]
    _ = (E c)⁻¹ * (l * (c * algebraMap R F (v i))) := by rw [hi]
    _ = ((E c)⁻¹ * l * c) * algebraMap R F (v i) := by ring

/-- A normalized integral representative of a subspace's Plücker vector
inherits its invariant line from the actual invariant subspace. -/
theorem normalized_plucker_line_invariant {n r : ℕ}
    (U : Submodule F (Fin n → F)) (b : Basis (Fin r) F U)
    (e : R ≃+* R) (A : Matrix (Fin n) (Fin n) R)
    (v : Set.powersetCard (Fin n) r → R) (c : F) (hc : c ≠ 0)
    (hv : ∀ s, pluckerCoordinates (fun i => (b i : Fin n → F)) s =
      c * algebraMap R F (v s))
    (hU : ∀ w ∈ U, A.map (algebraMap R F) *ᵥ
      (fun i => IsFractionRing.ringEquivOfRingEquiv e (w i)) ∈ U) :
    ∃ l : F, ∀ s,
      algebraMap R F ((exteriorMatrix r A *ᵥ (fun t => e (v t))) s) =
        l * algebraMap R F (v s) := by
  classical
  apply semilinear_proportional_normalization e (exteriorMatrix r A)
    (pluckerCoordinates (fun i => (b i : Fin n → F))) v c hc hv
  obtain ⟨l, hl⟩ := semilinear_pluckerCoordinates_proportional U b
    (IsFractionRing.ringEquivOfRingEquiv e) (A.map (algebraMap R F)) hU
  refine ⟨l, ?_⟩
  rw [exteriorMatrix_map] at hl
  exact hl

/-- Compound matrices send a scalar matrix to the corresponding scalar
power, including the zeroth exterior power. -/
theorem exteriorMatrix_smul_one {n : ℕ} (r : ℕ) (a : F) :
    exteriorMatrix r (a • (1 : Matrix (Fin n) (Fin n) F)) = a ^ r • 1 := by
  classical
  unfold exteriorMatrix
  rw [map_smul, Matrix.toLin'_one, exteriorPower_map_smul_id,
    map_smul, LinearMap.toMatrix_id]

/-- A nonzero fixed tuple of exterior coordinates detects the full
central-weight divisibility. -/
theorem exteriorMatrix_fixed_scalar_divisibility {n r l e : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ l) (v : Set.powersetCard (Fin n) r → F) (hv : v ≠ 0)
    (hfixed : exteriorMatrix r (ζ ^ e • (1 : Matrix (Fin n) (Fin n) F)) *ᵥ v = v) :
    l ∣ e * r := by
  classical
  apply (hζ.pow_eq_one_iff_dvd _).mp
  apply smul_left_injective F hv
  simpa only [exteriorMatrix_smul_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← pow_mul, one_smul] using hfixed

end Froberg
