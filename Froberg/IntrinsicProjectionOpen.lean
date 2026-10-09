module

public import Froberg.IntrinsicProjection
public import Froberg.BilinearScalarSurjection

@[expose] public section

/-! The uniform projection theorem in the actual vector spaces, with its
kernel dimension established from the same uniform growth estimate. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module Quartic MvPolynomial
open BilinearScalarFamily PolynomialBilinearCoordinates
variable {K F V W : Type*} [Field K] [Infinite K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- An actual quotient of the prescribed dimension satisfies normalized
image growth on every source subspace at once. -/
abbrev ProjectionParameter (K : Type*) [Field K] (W : Type*) [AddCommGroup W] [Module K W] (b : ℕ) :=
  Fin (finrank K ((Fin (finrank K W) → K) →ₗ[K] (Fin b → K)))

def coordinateProjection {b : ℕ} (x : ProjectionParameter K W b → K) :
    W →ₗ[K] (Fin b → K) :=
  ((Module.finBasis K ((Fin (finrank K W) → K) →ₗ[K] (Fin b → K))).equivFun.symm x).comp
    (coordinates K W).toLinearMap

theorem coordinateProjection_surjective (b : ℕ) :
    Function.Surjective (coordinateProjection (K := K) (W := W) (b := b)) := by
  intro P
  refine ⟨(Module.finBasis K ((Fin (finrank K W) → K) →ₗ[K] (Fin b → K))).equivFun
    (P.comp (coordinates K W).symm.toLinearMap),?_⟩
  ext w
  simp only [coordinateProjection,LinearEquiv.symm_apply_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

theorem coordinateProjection_polynomial (b : ℕ) :
    IsPolynomialFamily (coordinateProjection (K := K) (W := W) (b := b)) := by
  let L : (ProjectionParameter K W b → K) →ₗ[K] (W →ₗ[K] (Fin b → K)) :=
    { toFun := coordinateProjection
      map_add' := by
        intro x y
        ext w i
        simp only [coordinateProjection,map_add,LinearMap.add_comp,LinearMap.add_apply,Pi.add_apply]
      map_smul' := by
        intro c x
        ext w i
        simp only [coordinateProjection,map_smul,LinearMap.smul_comp,LinearMap.smul_apply,Pi.smul_apply,RingHom.id_apply] }
  exact isPolynomialFamily_linear L

theorem normalized_projection_principal_open {u b : ℕ}
    (ha : 0 < finrank K V) (hW : finrank K W = u+b)
    (hmargin : finrank K V*finrank K V < u*b)
    (mu : F →ₗ[K] V →ₗ[K] W)
    (hmu : ∀ L : Submodule K V,
      finrank K W * finrank K L ≤ finrank K V * finrank K (BilinearImage.image mu L)) :
    ∃ D : MvPolynomial (ProjectionParameter K W b) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 →
      Function.Surjective (coordinateProjection x) ∧ finrank K (coordinateProjection x).ker=u ∧
      ∀ L : Submodule K V,
        b*finrank K L ≤ finrank K V*finrank K ((BilinearImage.image mu L).map (coordinateProjection x)) := by
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
  obtain ⟨D,hDne,hD⟩ := normalized_projection_open ha hW hmargin mu' hmu'
  refine ⟨D,hDne,?_⟩
  intro x hx
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
  refine ⟨hsurj,?_,hgood⟩
  change finrank K P.ker=u
  have hd := LinearMap.finrank_range_add_finrank_ker P
  rw [htop,finrank_top] at hd
  simp only [Module.finrank_pi_fintype,finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] at hd
  omega

end Froberg
