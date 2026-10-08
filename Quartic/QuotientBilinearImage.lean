import Quartic.BilinearImage
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Ambient incidence for quotient multiplication images

Subspaces in V/E correspond to ambient subspaces containing E. Their full
bilinear images are the target quotient images of the ambient products.
When the target relations are precisely the products of E, dimensions differ
by one fixed relation-space dimension. This avoids variable quotient bases
in projective expansion certificates.
-/
noncomputable section
namespace Quartic.QuotientBilinearImage
open Module
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The actual induced bilinear multiplication on both quotients. -/
def quotientMap (mu : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V) :
    F →ₗ[K] (V ⧸ E) →ₗ[K] (W ⧸ BilinearImage.image mu E) where
  toFun f := E.liftQ ((BilinearImage.image mu E).mkQ.comp (mu f)) (by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr (BilinearImage.product_mem mu E f v hv))
  map_add' f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := E.mkQ_surjective x
    change (BilinearImage.image mu E).mkQ (mu (f+g) v) =
      (BilinearImage.image mu E).mkQ (mu f v) + (BilinearImage.image mu E).mkQ (mu g v)
    simp
  map_smul' s f := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,rfl⟩ := E.mkQ_surjective x
    change (BilinearImage.image mu E).mkQ (mu (s • f) v) = s • (BilinearImage.image mu E).mkQ (mu f v)
    simp

@[simp] theorem quotientMap_mk (mu : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V) (f : F) (v : V) :
    quotientMap mu E f (E.mkQ v) = (BilinearImage.image mu E).mkQ (mu f v) := rfl

/-- Dimension of the quotient image of a subspace containing all relations. -/
theorem finrank_map_mkQ_add [FiniteDimensional K W] (R S : Submodule K W) (hRS : R ≤ S) :
    finrank K (S.map R.mkQ) + finrank K R = finrank K S := by
  let f := R.mkQ.comp S.subtype
  have hr : LinearMap.range f = S.map R.mkQ := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have hk : LinearMap.ker f = R.comap S.subtype := by
    rw [LinearMap.ker_comp,Submodule.ker_mkQ]
  have hn := f.finrank_range_add_finrank_ker
  rw [hr,hk,(Submodule.comapSubtypeEquivOfLe hRS).finrank_eq] at hn
  exact hn

 theorem le_preimage (E : Submodule K V) (L : Submodule K (V ⧸ E)) :
    E ≤ L.comap E.mkQ := by
  intro v hv
  change E.mkQ v ∈ L
  have hz : E.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero E).mpr hv
  rw [hz]
  exact L.zero_mem

 theorem finrank_preimage [FiniteDimensional K V] (E : Submodule K V)
    (L : Submodule K (V ⧸ E)) :
    finrank K (L.comap E.mkQ) = finrank K L + finrank K E := by
  have h := finrank_map_mkQ_add E (L.comap E.mkQ) (le_preimage E L)
  rw [Submodule.map_comap_eq_of_surjective E.mkQ_surjective] at h
  exact h.symm

/-- The actual multiplication image commutes with passage to both quotients. -/
theorem image_eq_map (mu : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V) (R : Submodule K W)
    (nu : F →ₗ[K] (V ⧸ E) →ₗ[K] (W ⧸ R))
    (hcomm : ∀ f v, nu f (E.mkQ v) = R.mkQ (mu f v))
    (L : Submodule K (V ⧸ E)) :
    BilinearImage.image nu L = (BilinearImage.image mu (L.comap E.mkQ)).map R.mkQ := by
  unfold BilinearImage.image
  rw [Submodule.map_iSup]
  congr 1
  funext f
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,rfl⟩ := E.mkQ_surjective x
    refine ⟨mu f v,⟨v,hx,rfl⟩,?_⟩
    exact (hcomm f v).symm
  · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨E.mkQ v,hv,hcomm f v⟩

 theorem image_mono (mu : F →ₗ[K] V →ₗ[K] W) {S T : Submodule K V} (hST : S ≤ T) :
    BilinearImage.image mu S ≤ BilinearImage.image mu T := by
  apply iSup_le
  intro f
  exact (Submodule.map_mono hST).trans (le_iSup (fun f : F => T.map (mu f)) f)

/-- If the relations are the full product image of E, quotient-image ranks
are exactly ambient product ranks minus that fixed relation rank. -/
theorem image_finrank_add [FiniteDimensional K W]
    (mu : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V)
    (nu : F →ₗ[K] (V ⧸ E) →ₗ[K] (W ⧸ BilinearImage.image mu E))
    (hcomm : ∀ f v, nu f (E.mkQ v) = (BilinearImage.image mu E).mkQ (mu f v))
    (L : Submodule K (V ⧸ E)) :
    finrank K (BilinearImage.image nu L) + finrank K (BilinearImage.image mu E) =
      finrank K (BilinearImage.image mu (L.comap E.mkQ)) := by
  rw [image_eq_map mu E _ nu hcomm L]
  exact finrank_map_mkQ_add _ _ (image_mono mu (le_preimage E L))

/-- Expansion in the quotient is equivalent to a fixed-ambient statement on
all planes containing the presentation. Both dimension shifts are exact. -/
theorem expansion_iff_ambient [FiniteDimensional K V] [FiniteDimensional K W]
    (mu : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V) (d e : ℕ) :
    (∀ L : Submodule K (V ⧸ E), finrank K L = d →
      e ≤ finrank K (BilinearImage.image (quotientMap mu E) L)) ↔
    (∀ S : Submodule K V, E ≤ S → finrank K S = d + finrank K E →
      e + finrank K (BilinearImage.image mu E) ≤ finrank K (BilinearImage.image mu S)) := by
  constructor
  · intro h S hES hS
    let L := S.map E.mkQ
    have hL : finrank K L = d := by
      change finrank K (S.map E.mkQ) = d
      have hdim := finrank_map_mkQ_add E S hES
      omega
    have hback : L.comap E.mkQ = S := by
      rw [Submodule.comap_map_mkQ,sup_eq_right.mpr hES]
    have hi := image_finrank_add mu E (quotientMap mu E) (quotientMap_mk mu E) L
    rw [hback] at hi
    have hb := h L hL
    omega
  · intro h L hL
    have hdim : finrank K (L.comap E.mkQ) = d + finrank K E := by
      rw [finrank_preimage,hL]
    have hb := h (L.comap E.mkQ) (le_preimage E L) hdim
    have hi := image_finrank_add mu E (quotientMap mu E) (quotientMap_mk mu E) L
    omega

end Quartic.QuotientBilinearImage
