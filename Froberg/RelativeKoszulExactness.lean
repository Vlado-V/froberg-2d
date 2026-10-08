import Froberg.Graded
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Relative multiplication after adjoining generators. Exactness of the
combined cycle-boundary complex implies injectivity on the old coefficient
quotient and the literal dimension identity for the two target quotients. -/
noncomputable section
namespace Froberg.RelativeKoszul
open Module
variable {K U V W C ι : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] [AddCommGroup C] [Module K C]
variable [Fintype ι] [DecidableEq ι]

abbrev sourceRelations (R : Submodule K V) : Submodule K (ι → V) :=
  Submodule.pi Set.univ (fun _ => R)

/-- The quotient kernel consists precisely of old coefficient relations.
The two assumptions used for the reverse inclusion are exactness of the
combined complex and the support of the actual boundary in new coordinates. -/
theorem relative_kernel (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V) (boundary : C →ₗ[K] U × (ι → V))
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range)
    (hcycles : (old.coprod fresh).ker ≤ boundary.range)
    (hboundary : ∀ c i, (boundary c).2 i ∈ R) :
    (old.range.mkQ.comp fresh).ker = sourceRelations (ι := ι) R := by
  ext v
  change old.range.mkQ (fresh v)=0 ↔ v ∈ sourceRelations R
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u,hu⟩
    have hcycle : (-u,v) ∈ (old.coprod fresh).ker := by
      change old (-u)+fresh v=0
      rw [map_neg,hu,neg_add_cancel]
    obtain ⟨c,hc⟩ := hcycles hcycle
    apply Submodule.mem_pi.mpr
    intro i _
    have hi := hboundary c i
    simpa only [hc] using hi
  · intro hv
    exact hrel v (fun i => Submodule.mem_pi.mp hv i (Set.mem_univ i))

theorem sourceRelations_le_kernel (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V)
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range) :
    sourceRelations (ι := ι) R ≤ (old.range.mkQ.comp fresh).ker := by
  intro v hv
  change old.range.mkQ (fresh v)=0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (hrel v (fun i => Submodule.mem_pi.mp hv i (Set.mem_univ i)))

/-- The relative map on one copy of the old coefficient quotient for each
new generator. Its target is the old target quotient. -/
def multiplication (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V)
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range) :
    (ι → V ⧸ R) →ₗ[K] W ⧸ old.range :=
  ((sourceRelations R).liftQ (old.range.mkQ.comp fresh)
    (sourceRelations_le_kernel old fresh R hrel)).comp
    (Submodule.quotientPi (fun _ : ι => R)).symm.toLinearMap

@[simp] theorem multiplication_mk (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V)
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range)
    (v : ι → V) :
    multiplication old fresh R hrel (fun i => R.mkQ (v i)) = old.range.mkQ (fresh v) := by
  have he : (Submodule.quotientPi (fun _ : ι => R)).symm (fun i => R.mkQ (v i)) =
      (sourceRelations R).mkQ v := by
    apply (Submodule.quotientPi (fun _ : ι => R)).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [multiplication,LinearMap.comp_apply,LinearEquiv.coe_coe,he]
  rfl

/-- Combined Koszul exactness rules out every extra relative relation. -/
theorem multiplication_injective (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V) (boundary : C →ₗ[K] U × (ι → V))
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range)
    (hcycles : (old.coprod fresh).ker ≤ boundary.range)
    (hboundary : ∀ c i, (boundary c).2 i ∈ R) :
    Function.Injective (multiplication old fresh R hrel) := by
  have hi : Function.Injective ((sourceRelations R).liftQ (old.range.mkQ.comp fresh)
      (sourceRelations_le_kernel old fresh R hrel)) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.ker_liftQ_eq_bot
    exact (relative_kernel old fresh R boundary hrel hcycles hboundary).le
  exact hi.comp (Submodule.quotientPi (fun _ : ι => R)).symm.injective

theorem multiplication_range (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V)
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range) :
    (multiplication old fresh R hrel).range = fresh.range.map old.range.mkQ := by
  rw [multiplication,LinearMap.range_comp,
    LinearEquiv.range,Submodule.map_top,Submodule.range_liftQ,LinearMap.range_comp]

/-- Projection from the old target quotient to the quotient after adjoining
all new products. -/
def targetProjection (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W) :
    (W ⧸ old.range) →ₗ[K] W ⧸ (old.range ⊔ fresh.range) :=
  old.range.mapQ (old.range ⊔ fresh.range) LinearMap.id le_sup_left

theorem targetProjection_surjective (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W) :
    Function.Surjective (targetProjection old fresh) := by
  intro y
  obtain ⟨w,rfl⟩ := (old.range ⊔ fresh.range).mkQ_surjective y
  exact ⟨old.range.mkQ w,rfl⟩

theorem targetProjection_kernel (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W) :
    (targetProjection old fresh).ker = fresh.range.map old.range.mkQ := by
  have hz : old.range.map old.range.mkQ=⊥ := Submodule.mkQ_map_self _
  rw [targetProjection,Submodule.ker_mapQ,Submodule.comap_id,
    Submodule.map_sup,hz,bot_sup_eq]

/-- C.21 at the level of literal subspace quotients. -/
theorem target_finrank [FiniteDimensional K V] [FiniteDimensional K W]
    (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V) (boundary : C →ₗ[K] U × (ι → V))
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range)
    (hcycles : (old.coprod fresh).ker ≤ boundary.range)
    (hboundary : ∀ c i, (boundary c).2 i ∈ R) :
    finrank K (W ⧸ old.range) =
      finrank K (W ⧸ (old.range ⊔ fresh.range)) + Fintype.card ι * finrank K (V ⧸ R) := by
  have hd := (targetProjection old fresh).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (targetProjection_surjective old fresh),finrank_top,
    targetProjection_kernel,←multiplication_range old fresh R hrel,
    LinearMap.finrank_range_of_inj (multiplication_injective old fresh R boundary hrel hcycles hboundary)] at hd
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul] using hd.symm

end Froberg.RelativeKoszul
