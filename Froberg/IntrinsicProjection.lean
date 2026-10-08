import Froberg.NormalizedProjection
import Froberg.BilinearScalarSurjection

/-! The uniform projection theorem in the actual vector spaces, with its
kernel dimension established from the same uniform growth estimate. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic
open BilinearScalarFamily PolynomialBilinearCoordinates
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- An actual quotient of the prescribed dimension satisfies normalized
image growth on every source subspace at once. -/
theorem exists_normalized_projection {u b : ℕ}
    (ha : 0 < finrank K V) (hW : finrank K W = u+b)
    (hmargin : finrank K V*finrank K V < u*b)
    (mu : F →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ L : Submodule K V,
      finrank K W * finrank K L ≤ finrank K V * finrank K (BilinearImage.image mu L)) :
    ∃ P : W →ₗ[K] (Fin b → K), Function.Surjective P ∧ finrank K P.ker = u ∧
      ∀ L : Submodule K V,
        b*finrank K L ≤ finrank K V*finrank K ((BilinearImage.image mu L).map P) := by
  let eF := coordinates K F
  let eV := coordinates K V
  let eW := coordinates K W
  let mu' := transportBilinear eF eV eW mu
  have hmu' (L : Submodule K (Fin (finrank K V) → K)) :
      finrank K W*finrank K L ≤ finrank K V*finrank K (BilinearImage.image mu' L) := by
    have hh := hmu (L.map eV.symm.toLinearMap)
    rw [eV.symm.finrank_map_eq] at hh
    change _ ≤ finrank K V*finrank K (BilinearImage.image (transportBilinear eF eV eW mu) L)
    rw [image_transportBilinear,eW.finrank_map_eq]
    exact hh
  obtain ⟨D,⟨x,hx⟩,hD⟩ := normalized_projection_open ha hW hmargin mu' hmu'
  let P' := (Module.finBasis K ((Fin (finrank K W) → K) →ₗ[K] (Fin b → K))).equivFun.symm x
  let P := P'.comp eW.toLinearMap
  have hgood (L : Submodule K V) :
      b*finrank K L ≤ finrank K V*finrank K ((BilinearImage.image mu L).map P) := by
    have hh := hD x hx (L.map eV.toLinearMap)
    rw [eV.finrank_map_eq] at hh
    change _ ≤ finrank K V*finrank K ((BilinearImage.image (transportBilinear eF eV eW mu)
      (L.map eV.toLinearMap)).map P') at hh
    rw [image_transportBilinear] at hh
    have he : (L.map eV.toLinearMap).map eV.symm.toLinearMap=L := by
      rw [← Submodule.map_comp]
      simp only [LinearEquiv.symm_comp,Submodule.map_id]
    rw [he,← Submodule.map_comp] at hh
    exact hh
  have hle : (BilinearImage.image mu (⊤ : Submodule K V)).map P ≤ P.range := by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨v,rfl⟩
  have hr : b ≤ finrank K P.range := by
    have hh := hgood (⊤ : Submodule K V)
    rw [finrank_top] at hh
    have hd := Submodule.finrank_mono hle
    nlinarith
  have htop : P.range=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm P.range.finrank_le (by simpa using hr)
  have hsurj : Function.Surjective P := LinearMap.range_eq_top.mp htop
  refine ⟨P,hsurj,?_,hgood⟩
  have hd := LinearMap.finrank_range_add_finrank_ker P
  rw [htop,finrank_top] at hd
  simp only [Module.finrank_pi_fintype,finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] at hd
  omega

end Froberg
