import Quartic.SplitBlock22MiddleHomology
import Quartic.SplitBlock31Projection
import Quartic.CubicLinearCoordinates

/-!
# Projections of actual split quadrics for the (2,2) block

These maps read the pure-child, mixed, and pure-core components of a full
quadric. Their recovery and vanishing identities establish coordinate
compatibility for the full indexed Koszul complex.
-/
noncomputable section
namespace Quartic.SplitBlock22
open Module MvPolynomial SplitTensor
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q : ℕ}

private theorem tensor_family_injective {I X Y : Type*} [Fintype I]
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

/-- The mixed coefficient array represents its actual polynomial faithfully. -/
theorem mixedEmbedding_injective : Function.Injective (mixedEmbedding (K := K) (m := m)) := by
  apply SplitTensor.polynomialEmbedding_injective.comp
  apply tensor_family_injective
  have he : (fun i : Fin 3 => (⟨X i, isHomogeneous_X K i⟩ : Forms K 3 1)) =
      CubicLinearCoordinates.variableBasis K (Fin 3) := by
    funext i
    apply Subtype.ext
    simp
  rw [he]
  exact (CubicLinearCoordinates.variableBasis K (Fin 3)).linearIndependent

/-- Read the same actual mixed polynomial in the child-first coordinates used by the (3,1) block. -/
def traceCoordinates : MiddleCoordinates.Mixed K m →ₗ[K] (Fin m → Forms K 3 1) :=
  SplitBlock31.linearYProjection.comp mixedEmbedding

/-- The two orientations reconstruct exactly the same full polynomial. -/
@[simp] theorem linearYEmbed_traceCoordinates (g : MiddleCoordinates.Mixed K m) :
    SplitBlock31.linearYEmbed (traceCoordinates g) = mixedEmbedding g := by
  have hm : mixedEmbedding g ∈ LinearMap.range (SplitBlock31.linearYEmbed (K := K) (m := m) (d := 1)) := by
    rw [SplitBlock31.range_linearYEmbed, ← SplitTensor.polynomialEmbedding_range]
    exact ⟨sumTensorLeft (fun i : Fin 3 => (⟨X i, isHomogeneous_X K i⟩ : Forms K 3 1)) g, rfl⟩
  obtain ⟨a, ha⟩ := hm
  change SplitBlock31.linearYEmbed (SplitBlock31.linearYProjection (mixedEmbedding g)) = _
  rw [← ha, SplitBlock31.linearYProjection_linearYEmbed]

/-- Project a full quadric to its actual mixed coefficient array. -/
def middleProjection : Forms K (3 + m) 2 →ₗ[K] MiddleCoordinates.Mixed K m :=
  (mixedEmbedding (K := K) (m := m)).leftInverse.comp
    (SplitBlock31.linearYEmbed.comp SplitBlock31.linearYProjection)

@[simp] theorem middleProjection_mixedEmbedding (g : MiddleCoordinates.Mixed K m) :
    middleProjection (mixedEmbedding g) = g := by
  change (mixedEmbedding (K := K) (m := m)).leftInverse
    (SplitBlock31.linearYEmbed (traceCoordinates g)) = g
  rw [linearYEmbed_traceCoordinates]
  exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr mixedEmbedding_injective) g

@[simp] theorem middleProjection_coreEmbed (p : Forms K 3 2) :
    middleProjection (SplitBlock31.coreEmbed (m := m) p) = 0 := by simp [middleProjection]

@[simp] theorem middleProjection_childEmbed (p : Forms K m 2) :
    middleProjection (SplitBlock31.childEmbed p) = 0 := by simp [middleProjection]

@[simp] theorem coreProjection_mixedEmbedding (g : MiddleCoordinates.Mixed K m) :
    SplitBlock31.coreProjection (mixedEmbedding g) = 0 := by
  simpa only [linearYEmbed_traceCoordinates] using
    SplitBlock31.coreProjection_linearYEmbed (traceCoordinates g)

/-- Set the three core variables to zero, retaining the child variables. -/
def dropCore : Poly K (3 + m) →ₐ[K] Poly K m :=
  aeval (Fin.addCases (fun _ : Fin 3 => 0) (fun i : Fin m => X i))

@[simp] theorem dropCore_X_core (i : Fin 3) :
    dropCore (K := K) (m := m) (X (Fin.castAdd m i)) = 0 := by simp [dropCore]

@[simp] theorem dropCore_X_child (i : Fin m) :
    dropCore (K := K) (X (Fin.natAdd 3 i)) = X i := by simp [dropCore]

@[simp] theorem dropCore_rename_child (p : Poly K m) :
    dropCore (rename (Fin.natAdd 3) p) = p := by
  have he : (dropCore (K := K) (m := m)).comp (rename (Fin.natAdd 3)) = AlgHom.id K _ := by
    ext i
    simp
  exact AlgHom.congr_fun he p

theorem dropCore_rename_core (p : Poly K 3) :
    dropCore (m := m) (rename (Fin.castAdd m) p) = C (p.coeff 0) := by
  have he : (dropCore (K := K) (m := m)).comp (rename (Fin.castAdd m)) =
      aeval (fun _ : Fin 3 => (0 : Poly K m)) := by ext i; simp
  have h := AlgHom.congr_fun he p
  exact h.trans (eval₂_zero_apply C p)

/-- The child quadratic component of any actual full quadric. -/
def childProjection : Forms K (3 + m) 2 →ₗ[K] Forms K m 2 :=
  (dropCore.toLinearMap.comp (Forms K (3 + m) 2).subtype).codRestrict _ (fun p => by
    change (dropCore p.val).IsHomogeneous 2
    have hh : ∀ i : Fin (3+m),
        (Fin.addCases (fun _ : Fin 3 => (0 : Poly K m)) (fun j : Fin m => (X j : Poly K m)) i : Poly K m).IsHomogeneous 1 := by
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.addCases_left]
        exact (Forms K m 1).zero_mem
      · intro j; simpa using isHomogeneous_X K j
    simpa [dropCore] using p.property.aeval _ hh)

@[simp] theorem childProjection_childEmbed (p : Forms K m 2) :
    childProjection (SplitBlock31.childEmbed p) = p := by
  apply Subtype.ext
  exact dropCore_rename_child p.val

@[simp] theorem childProjection_coreEmbed (p : Forms K 3 2) :
    childProjection (SplitBlock31.coreEmbed (m := m) p) = 0 := by
  apply Subtype.ext
  change dropCore (rename (Fin.castAdd m) p.val) = 0
  rw [dropCore_rename_core, p.property.coeff_eq_zero (by simp), map_zero]

@[simp] theorem childProjection_mixedEmbedding (g : MiddleCoordinates.Mixed K m) :
    childProjection (mixedEmbedding g) = 0 := by
  apply Subtype.ext
  change dropCore (mixedEmbedding g).val = 0
  rw [mixedEmbedding_val, map_sum]
  simp

end Quartic.SplitBlock22
