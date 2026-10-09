module

public import Quartic.SplitBlock22
public import Quartic.Homology

@[expose] public section

/-!
# Canonical homology reduction in actual bidegree (2,2)

Projecting a cycle to its mixed coefficients identifies the quotient by
pure–child Koszul boundaries with the kernel of the actual middle quotient
map. A second quotient removes the actual mixed–mixed Koszul boundaries.
-/
noncomputable section
namespace Quartic.SplitBlock22
open Module MvPolynomial ThreeBlockModel SplitTensor
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q : ℕ}

private theorem sumTensorLeft_injective {I X Y : Type*} [Fintype I]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (v : I → X) (hv : LinearIndependent K v) :
    Function.Injective (sumTensorLeft (K := K) (Y := Y) v) := by
  classical
  obtain ⟨r, hr⟩ := (Fintype.linearCombination K v).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  have hrvi (i : I) : r (v i) = Pi.single i 1 := by
    have h := congrArg (fun f : (I → K) →ₗ[K] (I → K) => f (Pi.single i 1)) hr
    simpa using h
  let recover : X ⊗[K] Y →ₗ[K] (I → Y) :=
    (TensorProduct.piScalarRight K K Y I).toLinearMap.comp
      ((TensorProduct.comm K (I → K) Y).toLinearMap.comp
        (TensorProduct.map r (LinearMap.id : Y →ₗ[K] Y)))
  have hrec (a : I → Y) : recover (sumTensorLeft v a) = a := by
    funext i
    simp [recover, sumTensorLeft_apply, hrvi, Pi.single_apply]
  exact Function.LeftInverse.injective hrec

/-- Independence of the fixed four pure quadrics makes their coefficient map injective. -/
theorem pureMap_injective : Function.Injective (pureMap (K := K) (m := m)) :=
  sumTensorLeft_injective blockQuadrics blockQuadrics_independent

/-- Independent child quadrics likewise have no relation with constant pure coefficients. -/
theorem childMap_injective (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) :
    Function.Injective (childMap h) :=
  (TensorProduct.comm K _ _).injective.comp (sumTensorLeft_injective h hh)

abbrev Source (K : Type*) [Field K] (m c q : ℕ) :=
  (Fin 4 → Forms K m 2) × (Fin c → MiddleCoordinates.Mixed K m) × (Fin q → Forms K 3 2)

/-- Scalar coefficients of the actual pure–child generator pairs. -/
abbrev CrossCoefficients (K : Type*) (q : ℕ) := Fin 4 × Fin q → K

/-- The explicit incoming pure–child Koszul relation array. -/
def crossBoundary (h : Fin q → Forms K m 2) : CrossCoefficients K q →ₗ[K] Source K m c q where
  toFun b := (fun i => ∑ j, b (i,j) • h j, 0, fun j => -(∑ i, b (i,j) • blockQuadrics i))
  map_add' a b := by
    apply Prod.ext
    · funext i; simp [add_smul, Finset.sum_add_distrib]
    · apply Prod.ext
      · simp
      · funext j; simp [add_smul, Finset.sum_add_distrib, add_comm]
  map_smul' s a := by
    apply Prod.ext
    · funext i; simp [smul_smul, Finset.smul_sum]
    · apply Prod.ext
      · simp
      · funext j; simp [smul_smul, Finset.smul_sum]

/-- The common polynomial product represented by a pure–child boundary. -/
def crossProduct (h : Fin q → Forms K m 2) (b : CrossCoefficients K q) : Target K m :=
  ∑ i : Fin 4, ∑ j : Fin q, b (i,j) • (blockQuadrics i ⊗ₜ[K] h j)

@[simp] theorem pureMap_crossBoundary (h : Fin q → Forms K m 2) (b : CrossCoefficients K q) :
    pureMap (crossBoundary (c := c) h b).1 = crossProduct h b := by
  simp [pureMap_apply, crossBoundary, crossProduct, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

@[simp] theorem childMap_crossBoundary (h : Fin q → Forms K m 2) (b : CrossCoefficients K q) :
    childMap h (crossBoundary (c := c) h b).2.2 = -crossProduct h b := by
  change childMap h (-(fun j => ∑ i, b (i,j) • blockQuadrics i)) = -crossProduct h b
  rw [map_neg]
  apply congrArg (fun z : Target K m => -z)
  simp only [childMap_apply, TensorProduct.sum_tmul, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, crossProduct]
  exact Finset.sum_comm (β := Target K m) (γ := Fin q)

/-- Every displayed pure–child array is an actual cycle. -/
theorem crossBoundary_cycle (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (b : CrossCoefficients K q) :
    multiplication g h (crossBoundary h b) = 0 := by
  change pureMap (crossBoundary (c := c) h b).1 +
    (mixedMap g 0 + childMap h (crossBoundary (c := c) h b).2.2) = 0
  rw [map_zero, zero_add, pureMap_crossBoundary, childMap_crossBoundary]
  exact add_neg_cancel (crossProduct h b)

/-- Actual incoming pure–child boundary space in the full block source. -/
def crossSpace (h : Fin q → Forms K m 2) : Submodule K (Source K m c q) :=
  LinearMap.range (crossBoundary h)

theorem crossSpace_le_kernel (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) : crossSpace h ≤ (multiplication g h).ker := by
  rintro a ⟨b, rfl⟩
  exact crossBoundary_cycle g h b

/-- A cycle with zero mixed coefficients is exactly a pure–child Koszul boundary. -/
theorem cycle_zero_mixed_iff (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h)
    (a : Source K m c q) (ha : multiplication g h a = 0) :
    a.2.1 = 0 ↔ a ∈ crossSpace h := by
  constructor
  · intro ha0
    have he : pureMap a.1 + childMap h a.2.2 = 0 := by
      change pureMap a.1 + (mixedMap g a.2.1 + childMap h a.2.2) = 0 at ha
      simpa only [ha0, map_zero, zero_add] using ha
    have hm : pureMap a.1 ∈ crossImage (Submodule.span K (Set.range h)) := by
      rw [← pureImage_inf_childImage]
      constructor
      · rw [← pureMap_range]
        exact ⟨a.1, rfl⟩
      · rw [← childMap_range]
        refine ⟨-a.2.2, ?_⟩
        rw [map_neg]
        exact (eq_neg_of_add_eq_zero_left he).symm
    rw [crossImage_span] at hm
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    have hb' : crossProduct h b = pureMap a.1 := by
      simpa only [crossProduct, Fintype.sum_prod_type] using hb
    refine ⟨b, ?_⟩
    apply Prod.ext
    · apply pureMap_injective
      rw [pureMap_crossBoundary, hb']
    · apply Prod.ext
      · exact ha0.symm
      · apply childMap_injective h hh
        rw [childMap_crossBoundary, hb']
        calc
          -pureMap a.1 = -pureMap a.1 + (pureMap a.1 + childMap h a.2.2) := by rw [he, add_zero]
          _ = childMap h a.2.2 := by abel
  · rintro ⟨b, rfl⟩
    rfl

/-- The mixed coefficient projection, restricted to actual block cycles. -/
def cycleProjection (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) : (multiplication g h).ker →ₗ[K]
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))).ker :=
  ((LinearMap.fst K _ _).comp ((LinearMap.snd K _ _).comp (multiplication g h).ker.subtype)).codRestrict _
    (fun a => by
      apply (cycle_completion_iff h g a.val.2.1).mp
      refine ⟨a.val.1, a.val.2.2, ?_⟩
      have ha := a.property
      change pureMap a.val.1 + (mixedMap g a.val.2.1 + childMap h a.val.2.2) = 0 at ha
      rwa [add_assoc])

@[simp] theorem cycleProjection_val (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : (multiplication g h).ker) :
    (cycleProjection g h a).val = a.val.2.1 := rfl

/-- Every quotient-middle cycle is represented by an actual block cycle. -/
theorem cycleProjection_surjective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) : Function.Surjective (cycleProjection g h) := by
  intro a
  obtain ⟨b,d,hd⟩ := (cycle_completion_iff h g a.val).mpr a.property
  refine ⟨⟨(b,a.val,d), ?_⟩, ?_⟩
  · change pureMap b + (mixedMap g a.val + childMap h d) = 0
    rwa [← add_assoc]
  · apply Subtype.ext
    rfl

/-- The projection kernel is precisely the incoming pure–child boundaries. -/
theorem cycleProjection_ker (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) :
    (cycleProjection g h).ker = kernelBoundary (W := Target K m) (multiplication g h) (crossSpace (c := c) h) := by
  ext a
  change cycleProjection g h a = 0 ↔ a.val ∈ crossSpace h
  rw [← Subtype.val_inj]
  exact cycle_zero_mixed_iff g h hh a.val a.property

def quotientByKernel {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (B : Submodule K V)
    (hk : f.ker = B) (hs : Function.Surjective f) : (V ⧸ B) ≃ₗ[K] W :=
  (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)

/-- Canonical cycle quotient after eliminating exactly the pure–child Koszul boundaries. -/
def crossQuotientEquiv (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) :
    KernelModulo (W := Target K m) (multiplication g h) (crossSpace (c := c) h) ≃ₗ[K]
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))).ker :=
  quotientByKernel (K := K) (V := (multiplication g h).ker)
    (W := (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))).ker)
    (cycleProjection g h) _ (cycleProjection_ker g h hh)
    (cycleProjection_surjective g h)

@[simp] theorem crossQuotientEquiv_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : LinearIndependent K h) (a : (multiplication g h).ker) :
    crossQuotientEquiv g h hh (Submodule.Quotient.mk a) = cycleProjection g h a := by
  simp [crossQuotientEquiv, quotientByKernel]

end Quartic.SplitBlock22
