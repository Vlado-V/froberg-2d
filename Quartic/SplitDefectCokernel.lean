module

public import Quartic.ActualSplitCokernel

@[expose] public section

/-! The split cokernel bound without exactness of the child endpoint. -/
noncomputable section
namespace Quartic.SplitDefectCokernel
open Module MvPolynomial ActualSplitCokernel SplitBigrading
variable {K : Type*} [Field K] {m c q : ℕ}
set_option maxHeartbeats 1500000

abbrev ChildCokernel (h : Fin q → Forms K m 2) :=
  Forms K m 4 ⧸ (quadraticMultiplication h).range

def outerMap (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    RawJ g h →ₗ[K] Cokernel g h :=
  (GeneralF13.combined g h).range.liftQ
    ((quadraticMultiplication (SplitBlock22.fullGenerators g h)).range.mkQ.comp (rowEmbedding 3))
    (by
      rintro _ ⟨a,rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨sourceEmbedding13 a,multiplication_sourceEmbedding13 g h a⟩)

def childMap (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    ChildCokernel h →ₗ[K] Cokernel g h :=
  (quadraticMultiplication h).range.liftQ
    ((quadraticMultiplication (SplitBlock22.fullGenerators g h)).range.mkQ.comp SplitBlock31.childEmbed)
    (by
      rintro _ ⟨a,rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨sourceEmbedding04 a,multiplication_sourceEmbedding04 g h a⟩)

def fromComponents (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    RawJ g h × ChildCokernel h →ₗ[K] Cokernel g h :=
  (outerMap g h).coprod (childMap g h)

/-- All split cokernel classes come from the outer row or the pure child row. -/
theorem fromComponents_surjective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    Function.Surjective (fromComponents g h) := by
  intro z
  obtain ⟨p,rfl⟩ := (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range.mkQ_surjective z
  let I := (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range
  have hgen : ∀ j : Fin 5, I.mkQ (slice 4 j p) ∈ (fromComponents g h).range := by
    intro j
    fin_cases j
    · have hp : slice 4 (0 : Fin 5) p ∈ I := by
        apply SplitBlock40.pure_target_le_range (fun k => SplitBlock22.traceCoordinates (g k)) h
        rw [coreEmbed_range]
        exact ⟨component 0 p,rfl⟩
      change I.mkQ (slice 4 (0 : Fin 5) p) ∈ (fromComponents g h).range
      have hz : I.mkQ (slice 4 (0 : Fin 5) p) = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hp
      rw [hz]
      exact Submodule.zero_mem _
    · have hp : slice 4 (1 : Fin 5) p ∈ I := target31_le_range g h ⟨component 1 p,rfl⟩
      change I.mkQ (slice 4 (1 : Fin 5) p) ∈ (fromComponents g h).range
      have hz : I.mkQ (slice 4 (1 : Fin 5) p) = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hp
      rw [hz]
      exact Submodule.zero_mem _
    · have hp : slice 4 (2 : Fin 5) p ∈ I :=
        SplitBlock22.full_target_le_range g h h22 ⟨component 2 p,rfl⟩
      change I.mkQ (slice 4 (2 : Fin 5) p) ∈ (fromComponents g h).range
      have hz : I.mkQ (slice 4 (2 : Fin 5) p) = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hp
      rw [hz]
      exact Submodule.zero_mem _
    · refine ⟨((GeneralF13.combined g h).range.mkQ (projection13 p),0),?_⟩
      change I.mkQ (rowEmbedding 3 (projection13 p)) + (childMap g h) 0 = _
      rw [map_zero,add_zero,rowEmbedding_projection13]
      rfl
    · obtain ⟨a,ha⟩ : slice 4 (4 : Fin 5) p ∈ LinearMap.range
          (SplitBlock31.childEmbed (K := K) (m := m) (d := 4)) := by
        rw [childEmbed_range_four]
        exact ⟨component 4 p,rfl⟩
      refine ⟨(0,(quadraticMultiplication h).range.mkQ a),?_⟩
      change (outerMap g h) 0 + I.mkQ (SplitBlock31.childEmbed a) = _
      rw [map_zero,zero_add,ha]
      rfl
  have hp : I.mkQ p ∈ (fromComponents g h).range := by
    rw [← sum_slices p,map_sum]
    exact Submodule.sum_mem _ (fun j _ => hgen j)
  exact hp

/-- The child cokernel is the only extra term in the old split rank formula. -/
theorem cokernel_finrank_le (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    finrank K (Cokernel g h) ≤ finrank K (RawJ g h) + finrank K (ChildCokernel h) := by
  have hr := LinearMap.finrank_range_le (fromComponents g h)
  rw [LinearMap.range_eq_top.mpr (fromComponents_surjective g h h22),finrank_top,
    Module.finrank_prod] at hr
  exact hr

end Quartic.SplitDefectCokernel
