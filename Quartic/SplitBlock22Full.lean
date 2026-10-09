module

public import Quartic.SplitBlock22Coordinates

@[expose] public section

/-!
# The (2,2) source inside full indexed quartic multiplication

The full family is exactly the established pure/mixed/child family in the
(3,1) construction, using the two proven coordinate orientations of the
same mixed polynomials. The block source has a genuine retraction.
-/
noncomputable section
namespace Quartic.SplitBlock22
open Module MvPolynomial ThreeBlockModel
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q : ℕ}

/-- The existing full split family, written using middle coefficient coordinates. -/
def fullGenerators (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    Fin (4+(c+q)) → Forms K (3+m) 2 :=
  SplitBlock31.generators (fun j => traceCoordinates (g j)) h

@[simp] theorem fullGenerators_pure (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (i : Fin 4) :
    fullGenerators g h (Fin.castAdd (c+q) i) = SplitBlock31.coreEmbed (blockQuadrics i) := by
  simp [fullGenerators]

@[simp] theorem fullGenerators_mixed (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (i : Fin c) :
    fullGenerators g h (Fin.natAdd 4 (Fin.castAdd q i)) = mixedEmbedding (g i) := by
  simp [fullGenerators]

@[simp] theorem fullGenerators_child (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (i : Fin q) :
    fullGenerators g h (Fin.natAdd 4 (Fin.natAdd c i)) = SplitBlock31.childEmbed (h i) := by
  simp [fullGenerators]

/-- Insert exactly the coefficients of bidegree (2,2) into the full indexed source. -/
def sourceEmbedding : Source K m c q →ₗ[K] (Fin (4+(c+q)) → Forms K (3+m) 2) where
  toFun a := Fin.addCases (fun i => SplitBlock31.childEmbed (a.1 i))
    (Fin.addCases (fun j => mixedEmbedding (a.2.1 j)) (fun k => SplitBlock31.coreEmbed (a.2.2 k)))
  map_add' a b := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  map_smul' s a := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; refine Fin.addCases ?_ ?_ j <;> intro k <;> simp

@[simp] theorem sourceEmbedding_pure (a : Source K m c q) (i : Fin 4) :
    sourceEmbedding a (Fin.castAdd (c+q) i) = SplitBlock31.childEmbed (a.1 i) := by
  simp [sourceEmbedding]

@[simp] theorem sourceEmbedding_mixed (a : Source K m c q) (j : Fin c) :
    sourceEmbedding a (Fin.natAdd 4 (Fin.castAdd q j)) = mixedEmbedding (a.2.1 j) := by
  simp [sourceEmbedding]

@[simp] theorem sourceEmbedding_child (a : Source K m c q) (k : Fin q) :
    sourceEmbedding a (Fin.natAdd 4 (Fin.natAdd c k)) = SplitBlock31.coreEmbed (a.2.2 k) := by
  simp [sourceEmbedding]

/-- Read the child, mixed, and pure components on their corresponding generator slots. -/
def sourceProjection : (Fin (4+(c+q)) → Forms K (3+m) 2) →ₗ[K] Source K m c q :=
  (LinearMap.pi fun i : Fin 4 => childProjection.comp (LinearMap.proj (Fin.castAdd (c+q) i))).prod
    ((LinearMap.pi fun j : Fin c => middleProjection.comp
      (LinearMap.proj (Fin.natAdd 4 (Fin.castAdd q j)))).prod
    (LinearMap.pi fun k : Fin q => SplitBlock31.coreProjection.comp
      (LinearMap.proj (Fin.natAdd 4 (Fin.natAdd c k)))))

@[simp] theorem sourceProjection_sourceEmbedding (a : Source K m c q) :
    sourceProjection (sourceEmbedding a) = a := by
  apply Prod.ext
  · funext i
    change childProjection (sourceEmbedding a (Fin.castAdd (c+q) i)) = a.1 i
    simp
  · apply Prod.ext
    · funext j
      change middleProjection (sourceEmbedding a (Fin.natAdd 4 (Fin.castAdd q j))) = a.2.1 j
      simp
    · funext k
      change SplitBlock31.coreProjection (sourceEmbedding a (Fin.natAdd 4 (Fin.natAdd c k))) = a.2.2 k
      simp

theorem sourceEmbedding_injective : Function.Injective (sourceEmbedding (K := K) (m := m) (c := c) (q := q)) :=
  Function.LeftInverse.injective sourceProjection_sourceEmbedding

/-- The actual full polynomial multiplication restricts to the constructed (2,2) map. -/
theorem full_multiplication_commutes (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Source K m c q) :
    quadraticMultiplication (fullGenerators g h) (sourceEmbedding a) =
      targetEmbedding (multiplication g h a) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val]
  simp only [Fin.sum_univ_add, fullGenerators_pure, fullGenerators_mixed, fullGenerators_child,
    sourceEmbedding_pure, sourceEmbedding_mixed, sourceEmbedding_child,
    SplitBlock31.coreEmbed_val, SplitBlock31.childEmbed_val]
  simp only [multiplication, LinearMap.coprod_apply, map_add, Submodule.coe_add,
    pureMap_apply, childMap_apply, mixedMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, Submodule.coe_sum, targetEmbedding_tmul_val,
    mixedProduct_polynomial]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The embedded block has exactly its own multiplication kernel. -/
theorem sourceEmbedding_kernel (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Source K m c q) :
    quadraticMultiplication (fullGenerators g h) (sourceEmbedding a) = 0 ↔ multiplication g h a = 0 := by
  rw [full_multiplication_commutes]
  exact map_eq_zero_iff _ targetEmbedding_injective

end Quartic.SplitBlock22
