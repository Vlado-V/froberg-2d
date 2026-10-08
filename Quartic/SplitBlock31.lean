import Quartic.SplitBigrading
import Quartic.SplitMiddle31

/-!
# The (3,1) map inside the full polynomial multiplication map

The pure, mixed, and child generators are embedded into the actual polynomial
ring in `3+m` variables. The existing `(3,1)` source and target embed
injectively, and their multiplication map is the restriction of the full
quartic multiplication map on this explicit ordered generator family.
-/

noncomputable section
namespace Quartic.SplitBlock31
open Module MvPolynomial FreeCoefficients FreeMonomialCounts SplitBigrading
open ConvolutionLayers ConvolutionFreeMultiplication FreeCoefficientProducts
open ThreeBlockModel
variable {K : Type*} [Field K] {m c q d : ℕ}

/-- Embed a homogeneous X-polynomial by renaming to the first three variables. -/
def coreEmbed : Forms K 3 d →ₗ[K] Forms K (3 + m) d :=
  ((rename (Fin.castAdd m)).toLinearMap.comp (Forms K 3 d).subtype).codRestrict _
    (fun p => p.property.rename_isHomogeneous)

@[simp] theorem coreEmbed_val (p : Forms K 3 d) :
    (coreEmbed (m := m) p).val = rename (Fin.castAdd m) p.val := rfl

theorem coreEmbed_injective : Function.Injective (coreEmbed (K := K) (m := m) (d := d)) := by
  intro p r h
  apply Subtype.ext
  exact rename_injective _ (Fin.castAdd_injective 3 m) (congrArg Subtype.val h)

/-- Embed a homogeneous Y-polynomial by renaming to the last variables. -/
def childEmbed : Forms K m d →ₗ[K] Forms K (3 + m) d :=
  ((rename (Fin.natAdd 3)).toLinearMap.comp (Forms K m d).subtype).codRestrict _
    (fun p => p.property.rename_isHomogeneous)

@[simp] theorem childEmbed_val (p : Forms K m d) :
    (childEmbed p).val = rename (Fin.natAdd 3) p.val := rfl

/-- Insert one actual X-coefficient for each linear Y variable. -/
def linearYEmbed : (Fin m → Forms K 3 d) →ₗ[K] Forms K (3 + m) (d + 1) :=
  (embed (K := K) (t := 3) (w := m) (i := d) (j := 1)).comp
    (oneLayerEquiv (K := K) (w := m) (Forms K 3 d)).symm.toLinearMap

/-- Its represented polynomial is the expected sum of X coefficients times Y variables. -/
theorem linearYEmbed_val (a : Fin m → Forms K 3 d) :
    (linearYEmbed a).val = ∑ l : Fin m, liftCoeff (Finsupp.single l 1) (a l).val := by
  change blockPolynomial ((oneLayerEquiv (K := K) (w := m) (Forms K 3 d)).symm a) = _
  rw [blockPolynomial_apply]
  symm
  apply Fintype.sum_equiv (oneExponentEquiv (w := m))
  intro l
  simp [oneLayerEquiv]

/-- Extracting the coefficient of Y_l recovers its X-polynomial. -/
@[simp] theorem freeCoeff_linearYEmbed (a : Fin m → Forms K 3 d) (l : Fin m) :
    freeCoeff (Finsupp.single l 1) (linearYEmbed a).val = (a l).val := by
  classical
  rw [linearYEmbed_val, map_sum]
  simp only [freeCoeff_liftCoeff, Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)]
  simp

theorem linearYEmbed_injective : Function.Injective
    (linearYEmbed (K := K) (m := m) (d := d)) := by
  intro a b h
  funext l
  apply Subtype.ext
  simpa only [freeCoeff_linearYEmbed] using
    congrArg (fun p : Forms K (3 + m) (d + 1) => freeCoeff (Finsupp.single l 1) p.val) h

/-- The embedded coefficients are exactly the bidegree `(d,1)` component. -/
theorem range_linearYEmbed : LinearMap.range (linearYEmbed (K := K) (m := m) (d := d)) =
    bidegreeSpace K 3 m d 1 := by
  rw [linearYEmbed, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rfl

private theorem core_mul_lift (p : Poly K 3) (b : Fin m →₀ ℕ) (r : Poly K 3) :
    rename (Fin.castAdd m) p * liftCoeff b r = liftCoeff b (p * r) := by
  rw [← liftCoeff_zero_eq_rename p, liftCoeff_mul]
  simp

private theorem lift_mul_core (b : Fin m →₀ ℕ) (p r : Poly K 3) :
    liftCoeff b p * rename (Fin.castAdd m) r = liftCoeff b (r * p) := by
  rw [mul_comm, core_mul_lift]

/-- The ordered split family: four pure quadrics, then mixed quadrics, then child quadrics. -/
def generators (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2) :
    Fin (4 + (c + q)) → Forms K (3 + m) 2 :=
  Fin.addCases (fun i => coreEmbed (blockQuadrics i))
    (Fin.addCases (fun j => linearYEmbed (g j)) (fun k => childEmbed (Q k)))

/-- Embed all (3,1) coefficients in the actual source of quartic multiplication. -/
def sourceEmbedding : SplitMiddle31.Source K m c →ₗ[K]
    (Fin (4 + (c + q)) → Forms K (3 + m) 2) where
  toFun a := Fin.addCases (fun i => linearYEmbed (a.2 i))
    (Fin.addCases (fun j => coreEmbed (a.1 j)) (fun _ => 0))
  map_add' a b := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp
    · intro k
      refine Fin.addCases ?_ ?_ k <;> intro l <;> simp
  map_smul' s a := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp
    · intro k
      refine Fin.addCases ?_ ?_ k <;> intro l <;> simp

@[simp] theorem sourceEmbedding_pure (a : SplitMiddle31.Source K m c) (i : Fin 4) :
    sourceEmbedding (q := q) a (Fin.castAdd (c + q) i) = linearYEmbed (a.2 i) := by
  simp [sourceEmbedding]

@[simp] theorem sourceEmbedding_mixed (a : SplitMiddle31.Source K m c) (j : Fin c) :
    sourceEmbedding (q := q) a (Fin.natAdd 4 (Fin.castAdd q j)) = coreEmbed (a.1 j) := by
  simp [sourceEmbedding]

@[simp] theorem sourceEmbedding_child (a : SplitMiddle31.Source K m c) (k : Fin q) :
    sourceEmbedding (q := q) a (Fin.natAdd 4 (Fin.natAdd c k)) = 0 := by
  simp [sourceEmbedding]

theorem sourceEmbedding_injective : Function.Injective
    (sourceEmbedding (K := K) (m := m) (c := c) (q := q)) := by
  intro a b h
  apply Prod.ext
  · funext j
    apply coreEmbed_injective (m := m)
    simpa only [sourceEmbedding_mixed] using
      congrFun h (Fin.natAdd 4 (Fin.castAdd q j))
  · funext i
    apply linearYEmbed_injective
    simpa only [sourceEmbedding_pure] using congrFun h (Fin.castAdd (c + q) i)

/-- The actual full polynomial multiplication restricts to the existing (3,1) map. -/
theorem multiplication_commutes (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : SplitMiddle31.Source K m c) :
    quadraticMultiplication (generators g Q) (sourceEmbedding a) =
      linearYEmbed (SplitMiddle31.multiplication g a) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val, linearYEmbed_val]
  simp only [Fin.sum_univ_add, generators, Fin.addCases_left, Fin.addCases_right,
    sourceEmbedding_pure, sourceEmbedding_mixed, sourceEmbedding_child,
    coreEmbed_val, linearYEmbed_val, Submodule.coe_zero, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum, Finset.sum_mul, core_mul_lift, lift_mul_core]
  change (∑ i : Fin 4, ∑ l : Fin m,
      liftCoeff (Finsupp.single l 1) ((blockQuadrics i).val * (a.2 i l).val)) +
    (∑ j : Fin c, ∑ l : Fin m,
      liftCoeff (Finsupp.single l 1) ((a.1 j).val * (g j l).val)) = _
  rw [Finset.sum_comm (γ := Fin 4), Finset.sum_comm (γ := Fin c)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  change _ = liftCoeff (Finsupp.single l 1)
    ((∑ j : Fin c, (a.1 j).val * (g j l).val) +
      ∑ i : Fin 4, (blockQuadrics i).val * (a.2 i l).val)
  rw [map_add, map_sum, map_sum]
  exact add_comm _ _

/-- A (3,1) relation is a relation in the full actual quartic multiplication kernel. -/
theorem sourceEmbedding_kernel (g : SplitMiddle31.Mixed K m c) (Q : Fin q → Forms K m 2)
    (a : SplitMiddle31.Source K m c) :
    sourceEmbedding a ∈ LinearMap.ker (quadraticMultiplication (generators g Q)) ↔
      a ∈ LinearMap.ker (SplitMiddle31.multiplication g) := by
  change quadraticMultiplication (generators g Q) (sourceEmbedding a) = 0 ↔
    SplitMiddle31.multiplication g a = 0
  rw [multiplication_commutes]
  exact linearYEmbed_injective.eq_iff' (map_zero _)

end Quartic.SplitBlock31
