import Quartic.QuotientBilinearImage

/-! Fixed ambient covectors for varying quotient multiplication. -/
noncomputable section
namespace Quartic.QuotientCovectorKernel
open Module
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The source relation map associated to an actual target covector. -/
def relation (μ : F →ₗ[K] V →ₗ[K] W) (ell : W →ₗ[K] K) :
    V →ₗ[K] (F →ₗ[K] K) where
  toFun v := ell.comp (μ.flip v)
  map_add' v w := by ext f; simp
  map_smul' c v := by ext f; simp

@[simp] theorem relation_apply (μ : F →ₗ[K] V →ₗ[K] W)
    (ell : W →ₗ[K] K) (v : V) (f : F) : relation μ ell v f = ell (μ f v) := rfl

/-- Ambient annihilation of the relation space is exactly annihilation of
all products of the presentation generators. -/
theorem annihilates_image_iff (μ : F →ₗ[K] V →ₗ[K] W)
    (E : Submodule K V) (ell : W →ₗ[K] K) :
    BilinearImage.image μ E ≤ LinearMap.ker ell ↔
      ∀ f v, v ∈ E → ell (μ f v) = 0 := by
  constructor
  · intro h f v hv
    exact h (BilinearImage.product_mem μ E f v hv)
  · intro h
    apply iSup_le
    intro f
    rintro w ⟨v,hv,rfl⟩
    exact h f v hv

/-- The quotient relation map pulls back to the ambient relation map. -/
theorem relation_comp_mkQ (μ : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V)
    (ell : W →ₗ[K] K) (hrel : BilinearImage.image μ E ≤ LinearMap.ker ell) :
    (relation (QuotientBilinearImage.quotientMap μ E)
      ((BilinearImage.image μ E).liftQ ell hrel)).comp E.mkQ = relation μ ell := by
  ext v f
  rfl

/-- The ambient relation kernel is the full inverse image of the quotient
kernel, so it includes every presentation column. -/
theorem kernel_eq_comap (μ : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V)
    (ell : W →ₗ[K] K) (hrel : BilinearImage.image μ E ≤ LinearMap.ker ell) :
    LinearMap.ker (relation μ ell) =
      (LinearMap.ker (relation (QuotientBilinearImage.quotientMap μ E)
        ((BilinearImage.image μ E).liftQ ell hrel))).comap E.mkQ := by
  rw [← LinearMap.ker_comp,relation_comp_mkQ]

/-- The exact kernel-dimension shift allows all determinantal equations to
be written in fixed ambient coordinates, even as E varies. -/
theorem kernel_finrank [FiniteDimensional K V]
    (μ : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V)
    (ell : W →ₗ[K] K) (hrel : BilinearImage.image μ E ≤ LinearMap.ker ell) :
    finrank K (LinearMap.ker (relation μ ell)) =
      finrank K (LinearMap.ker (relation (QuotientBilinearImage.quotientMap μ E)
        ((BilinearImage.image μ E).liftQ ell hrel))) + finrank K E := by
  rw [kernel_eq_comap]
  exact QuotientBilinearImage.finrank_preimage E _

/-- A covector is nonzero before descent exactly when it is nonzero after descent. -/
theorem descended_eq_zero_iff (R : Submodule K W) (ell : W →ₗ[K] K)
    (hR : R ≤ LinearMap.ker ell) : R.liftQ ell hR = 0 ↔ ell = 0 := by
  constructor
  · intro h
    ext w
    exact congrArg (fun f : (W ⧸ R) →ₗ[K] K => f (R.mkQ w)) h
  · intro h
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := R.mkQ_surjective w
    change ell v = 0
    simp [h]

/-- The shared child-annihilation equations are unchanged by passing to
the source and target quotients. -/
theorem annihilates_source_iff (μ : F →ₗ[K] V →ₗ[K] W) (E : Submodule K V)
    (ell : W →ₗ[K] K) (hrel : BilinearImage.image μ E ≤ LinearMap.ker ell) (f : F) :
    (∀ v : V, ell (μ f v) = 0) ↔
      ∀ v : V ⧸ E, (BilinearImage.image μ E).liftQ ell hrel
        (QuotientBilinearImage.quotientMap μ E f v) = 0 := by
  constructor
  · intro h v
    obtain ⟨w,rfl⟩ := E.mkQ_surjective v
    exact h w
  · intro h v
    exact h (E.mkQ v)

end Quartic.QuotientCovectorKernel
