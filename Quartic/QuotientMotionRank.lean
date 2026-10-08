import Quartic.QuotientCovectorKernel
import Quartic.BilinearMotionConstraints

/-!
# Quotient-aware ranks of actual motion constraints

A raw coefficient space need not contain the presentation relations in
every component. Its relevant dimension is the dimension of its image in
the repeated quotient. Rank-nullity there loses at most k times the
quotient relation-kernel dimension, with no extra presentation term.
-/
noncomputable section
namespace Quartic.QuotientMotionRank
open Module CoefficientConstraintRank
variable {K V W T C : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup T] [Module K T]
  [AddCommGroup C] [Module K C]
  {k d : ℕ}

omit [FiniteDimensional K V] in
/-- Coordinatewise descent commutes with the actual repeated map. -/
theorem repeated_comp_quotient (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R) :
    (repeated (c := k) Rbar).comp (repeated E.mkQ)=repeated R := by
  apply LinearMap.ext
  intro x
  funext i
  exact LinearMap.congr_fun hcomm (x i)

omit [FiniteDimensional K V] in
/-- The repeated relation image of a raw subspace is exactly its quotient
image followed by the descended relation map. -/
theorem map_quotient_relation (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (U : Submodule K (Fin k → V)) :
    (U.map (repeated E.mkQ)).map (repeated Rbar)=U.map (repeated R) := by
  rw [← Submodule.map_comp,repeated_comp_quotient E R Rbar hcomm]

/-- Quotient-aware additive rank bound. No containment of E^k in U is
required: only the actual quotient coefficient image is measured. -/
theorem quotient_image_le_rank_add (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (U : Submodule K (Fin k → V)) :
    finrank K (U.map (repeated E.mkQ)) ≤
      finrank K (U.map (repeated R)) + k*d := by
  let S := U.map (repeated E.mkQ)
  have h := dimension_le_rank_add Rbar S.subtype Subtype.val_injective
  rw [LinearMap.range_comp,Submodule.range_subtype] at h
  have heq : S.map (repeated Rbar)=U.map (repeated R) :=
    map_quotient_relation E R Rbar hcomm U
  rw [heq] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k hker) _)

/-- The subtraction form of the same actual rank estimate. -/
theorem quotient_rank_bound (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (U : Submodule K (Fin k → V)) :
    finrank K (U.map (repeated E.mkQ))-k*d ≤ finrank K (U.map (repeated R)) := by
  have h := quotient_image_le_rank_add E R Rbar hcomm hker U
  omega

/-- Integer subtraction version for the manuscript's signed dimension counts. -/
theorem quotient_rank_bound_int (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (U : Submodule K (Fin k → V)) :
    (finrank K (U.map (repeated E.mkQ)) : ℤ)-(k:ℤ)*d ≤
      finrank K (U.map (repeated R)) := by
  have h := quotient_image_le_rank_add E R Rbar hcomm hker U
  have h' : (finrank K (U.map (repeated E.mkQ)) : ℤ) ≤
      (finrank K (U.map (repeated R)) : ℤ)+(k:ℤ)*d := by exact_mod_cast h
  omega

/-- Canonical descent from E contained in the ambient relation kernel. -/
theorem liftQ_rank_bound (E : Submodule K V) (R : V →ₗ[K] W)
    (hE : E ≤ LinearMap.ker R)
    (hker : finrank K (LinearMap.ker (E.liftQ R hE)) ≤ d)
    (U : Submodule K (Fin k → V)) :
    finrank K (U.map (repeated E.mkQ))-k*d ≤ finrank K (U.map (repeated R)) := by
  apply quotient_rank_bound E R (E.liftQ R hE) _ hker U
  ext x
  rfl

/-- An injective coefficient map into the repeated quotient supplies its
full source dimension, even when it is merely covered by a raw motion
coefficient space rather than lifted injectively to that space. -/
theorem coefficient_injection_le_rank_add (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (U : Submodule K (Fin k → V)) (coeff : T →ₗ[K] (Fin k → (V ⧸ E)))
    (hinj : Function.Injective coeff)
    (hcover : LinearMap.range coeff ≤ U.map (repeated E.mkQ)) :
    finrank K T ≤ finrank K (U.map (repeated R))+k*d := by
  have hdim : finrank K T ≤ finrank K (U.map (repeated E.mkQ)) := by
    rw [← LinearMap.finrank_range_of_inj hinj]
    exact Submodule.finrank_mono hcover
  exact hdim.trans (quotient_image_le_rank_add E R Rbar hcomm hker U)

/-- Interface for trace or correction coefficients represented by an
actual raw linear map. The coefficient map may have a different domain;
its injective range need only be covered after quotienting. -/
theorem coefficient_map_rank_bound (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (raw : C →ₗ[K] (Fin k → V)) (coeff : T →ₗ[K] (Fin k → (V ⧸ E)))
    (hinj : Function.Injective coeff)
    (hcover : LinearMap.range coeff ≤ LinearMap.range ((repeated E.mkQ).comp raw)) :
    finrank K T-k*d ≤ finrank K (LinearMap.range ((repeated R).comp raw)) := by
  have hcover' : LinearMap.range coeff ≤ (LinearMap.range raw).map (repeated E.mkQ) := by
    simpa only [LinearMap.range_comp] using hcover
  have h := coefficient_injection_le_rank_add E R Rbar hcomm hker
    (LinearMap.range raw) coeff hinj hcover'
  rw [← LinearMap.range_comp] at h
  omega

/-- A commuting actual lift is one sufficient way to verify coverage. -/
theorem coefficient_lift_rank_bound (E : Submodule K V) (R : V →ₗ[K] W)
    (Rbar : (V ⧸ E) →ₗ[K] W) (hcomm : Rbar.comp E.mkQ=R)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (raw : T →ₗ[K] (Fin k → V)) (coeff : T →ₗ[K] (Fin k → (V ⧸ E)))
    (hinj : Function.Injective coeff) (hlift : (repeated E.mkQ).comp raw=coeff) :
    finrank K T-k*d ≤ finrank K (LinearMap.range ((repeated R).comp raw)) := by
  apply coefficient_map_rank_bound E R Rbar hcomm hker raw coeff hinj
  rw [hlift]

section Bilinear
variable {F Y : Type*} [AddCommGroup F] [Module K F]
  [AddCommGroup Y] [Module K Y]

/-- The quotient-aware estimate for an actual target covector and actual
bilinear multiplication. The descended relation map is the literal
quotient multiplication relation, not an assumed rank model. -/
theorem actual_relation_rank_bound (μ : F →ₗ[K] V →ₗ[K] Y) (E : Submodule K V)
    (ell : Y →ₗ[K] K) (hrel : BilinearImage.image μ E ≤ LinearMap.ker ell)
    (hker : finrank K (LinearMap.ker
      (QuotientCovectorKernel.relation (QuotientBilinearImage.quotientMap μ E)
        ((BilinearImage.image μ E).liftQ ell hrel))) ≤ d)
    (U : Submodule K (Fin k → V)) :
    finrank K (U.map (repeated E.mkQ))-k*d ≤
      finrank K (U.map (repeated (QuotientCovectorKernel.relation μ ell))) :=
  quotient_rank_bound E _ _ (QuotientCovectorKernel.relation_comp_mkQ μ E ell hrel) hker U

end Bilinear

section Coordinates
open BilinearCoefficientKernel BilinearCovectorCharts
variable {a b D : ℕ} {N : Type*} [Fintype N]

/-- The existing literal motion matrix satisfies the sharp quotient-aware
bound for arbitrary spanning columns, whether or not they are independent. -/
theorem constraint_rank_bound
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin D → K))
    (ell : Fin D → K) (E : Submodule K (Fin a → K))
    (Rbar : ((Fin a → K) ⧸ E) →ₗ[K] (Fin b → K))
    (hcomm : Rbar.comp E.mkQ=relationMap mu ell)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (H : N → Fin k → Fin a → K) :
    finrank K ((Submodule.span K (Set.range H)).map (repeated E.mkQ))-k*d ≤
      (BilinearMotionConstraints.constraint mu ell H).rank := by
  rw [BilinearMotionConstraints.rank_eq]
  exact quotient_rank_bound E _ Rbar hcomm hker _

/-- Integer-valued form of the literal matrix estimate. -/
theorem constraint_rank_bound_int
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin D → K))
    (ell : Fin D → K) (E : Submodule K (Fin a → K))
    (Rbar : ((Fin a → K) ⧸ E) →ₗ[K] (Fin b → K))
    (hcomm : Rbar.comp E.mkQ=relationMap mu ell)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (H : N → Fin k → Fin a → K) :
    (finrank K ((Submodule.span K (Set.range H)).map (repeated E.mkQ)) : ℤ)-(k:ℤ)*d ≤
      (BilinearMotionConstraints.constraint mu ell H).rank := by
  rw [BilinearMotionConstraints.rank_eq]
  exact quotient_rank_bound_int E _ Rbar hcomm hker _

/-- Injected trace or correction coefficients, covered by the actual raw
spanning columns, impose their full dimension minus k*d conditions. -/
theorem constraint_coefficient_rank_bound
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin D → K))
    (ell : Fin D → K) (E : Submodule K (Fin a → K))
    (Rbar : ((Fin a → K) ⧸ E) →ₗ[K] (Fin b → K))
    (hcomm : Rbar.comp E.mkQ=relationMap mu ell)
    (hker : finrank K (LinearMap.ker Rbar) ≤ d)
    (H : N → Fin k → Fin a → K)
    (coeff : T →ₗ[K] (Fin k → ((Fin a → K) ⧸ E)))
    (hinj : Function.Injective coeff)
    (hcover : LinearMap.range coeff ≤
      (Submodule.span K (Set.range H)).map (repeated E.mkQ)) :
    finrank K T-k*d ≤ (BilinearMotionConstraints.constraint mu ell H).rank := by
  rw [BilinearMotionConstraints.rank_eq]
  have h := coefficient_injection_le_rank_add E _ Rbar hcomm hker _ coeff hinj hcover
  omega

end Coordinates
end Quartic.QuotientMotionRank
