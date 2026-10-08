import Quartic.SplitBlock40
import Quartic.SplitBlock22FullBoundaries
import Quartic.GeneralF13


/-!
# The actual full split cokernel

The explicit pure/mixed/child family in `3+m` variables has only its `(1,3)`
target quotient remaining when actual middle multiplication and child quartic
multiplication are surjective. This module proves the polynomial embedding and
projection identities, fills the other four bidegrees, and identifies the full
cokernel canonically with the actual ordinary-quotient F13 cokernel `J`.

Under independent child quadrics, injective child cubic multiplication, and
injective F13, the full split multiplication rank is `b4 (3+m) - j m q c`.
No source-homology exhaustion or split-rank premise is used. The map
`projectionJ` and its exact kernel identity are available for the subsequent
first-order and corrected second-order response calculations.
-/

noncomputable section
namespace Quartic.ActualSplitCokernel
open Module MvPolynomial SplitBigrading SplitTensor FreeCoefficients FreeMonomialCounts
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q d : ℕ}

/-- Coordinate rows are actual tensors with the three pure linear variables. -/
def rowsToTensor (d : ℕ) : (Fin 3 → Forms K m d) →ₗ[K] Forms K 3 1 ⊗[K] Forms K m d :=
  sumTensorLeft (CubicLinearCoordinates.variableBasis K (Fin 3))

def tensorToRows (d : ℕ) : (Forms K 3 1 ⊗[K] Forms K m d) →ₗ[K] (Fin 3 → Forms K m d) :=
  (TensorProduct.piScalarRight K K (Forms K m d) (Fin 3)).toLinearMap.comp
    ((TensorProduct.comm K (Fin 3 → K) (Forms K m d)).toLinearMap.comp
      (TensorProduct.map (CubicLinearCoordinates.variableBasis K (Fin 3)).equivFun.toLinearMap
        (LinearMap.id : Forms K m d →ₗ[K] Forms K m d)))

@[simp] theorem tensorToRows_rowsToTensor (a : Fin 3 → Forms K m d) :
    tensorToRows d (rowsToTensor d a) = a := by
  classical
  funext i
  simp [tensorToRows, rowsToTensor, sumTensorLeft_apply]

@[simp] theorem rowsToTensor_tensorToRows (a : Forms K 3 1 ⊗[K] Forms K m d) :
    rowsToTensor d (tensorToRows d a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [tensorToRows, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.comm_tmul, LinearMap.id_apply,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      rowsToTensor, sumTensorLeft_apply, TensorProduct.tmul_smul]
    simp_rw [TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, (CubicLinearCoordinates.variableBasis K (Fin 3)).sum_equivFun]
  | add a b ha hb => simp only [map_add, ha, hb]

def rowTensorEquiv (d : ℕ) : (Fin 3 → Forms K m d) ≃ₗ[K] Forms K 3 1 ⊗[K] Forms K m d :=
  { rowsToTensor d with
    invFun := tensorToRows d
    left_inv := tensorToRows_rowsToTensor
    right_inv := rowsToTensor_tensorToRows }

/-- Actual coordinates on every bidegree with pure degree one. -/
def rowBlockEquiv (d : ℕ) : (Fin 3 → Forms K m d) ≃ₗ[K] Block K 3 m 1 d :=
  (rowTensorEquiv d).trans biformEquiv

def rowEmbedding (d : ℕ) : (Fin 3 → Forms K m d) →ₗ[K] Forms K (3+m) (1+d) :=
  embed.comp (rowBlockEquiv d).toLinearMap

@[simp] theorem rowEmbedding_val (a : Fin 3 → Forms K m d) :
    (rowEmbedding d a).val = ∑ i : Fin 3, X (Fin.castAdd m i) * rename (Fin.natAdd 3) (a i).val := by
  change (polynomialEmbedding (rowsToTensor d a)).val = _
  simp [rowsToTensor, sumTensorLeft_apply]

theorem rowEmbedding_range : LinearMap.range (rowEmbedding (K := K) (m := m) d) =
    bidegreeSpace K 3 m 1 d := by
  rw [rowEmbedding, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rfl

@[simp] theorem rowEmbedding_one (g : MiddleCoordinates.Mixed K m) :
    rowEmbedding 1 g = SplitBlock22.mixedEmbedding g := by
  apply Subtype.ext
  rw [rowEmbedding_val, SplitBlock22.mixedEmbedding_val]

/-- The retained target component, in actual cubic row coordinates. -/
def projection13 : Forms K (3+m) 4 →ₗ[K] GeneralF13.Ambient K m :=
  (rowBlockEquiv 3).symm.toLinearMap.comp (component 3)

@[simp] theorem component_embed (u : Block K 3 m 1 3) : component 3 (embed u) = u := by
  funext b
  apply Subtype.ext
  exact freeCoeff_blockPolynomial u b

@[simp] theorem projection13_rowEmbedding (a : GeneralF13.Ambient K m) :
    projection13 (rowEmbedding 3 a) = a := by
  simp [projection13, rowEmbedding]

theorem projection13_surjective : Function.Surjective (projection13 (K := K) (m := m)) :=
  fun a => ⟨rowEmbedding 3 a, projection13_rowEmbedding a⟩

/-- Place one extracted bidegree back in the same actual homogeneous space. -/
def slice (d : ℕ) (j : Fin (d+1)) : Forms K (3+m) d →ₗ[K] Forms K (3+m) d where
  toFun p := ⟨blockPolynomial (component j.val p), by
    change (blockPolynomial (component j.val p)).IsHomogeneous d
    have hh := blockPolynomial_homogeneous (component j.val p)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)] using hh⟩
  map_add' p r := Subtype.ext (by simp [map_add])
  map_smul' s p := Subtype.ext (by simp [map_smul])

@[simp] theorem slice_val (d : ℕ) (j : Fin (d+1)) (p : Forms K (3+m) d) :
    (slice d j p).val = blockPolynomial (component j.val p) := rfl

theorem sum_slices (p : Forms K (3+m) d) : ∑ j : Fin (d+1), slice d j p = p := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, slice_val, SplitBigrading.join_val, SplitBigrading.split, LinearMap.pi_apply] using
    congrArg Subtype.val (SplitBigrading.join_split p)

theorem projection13_slice_ne (j : Fin 5) (hj : j.val ≠ 3) (p : Forms K (3+m) 4) :
    projection13 (slice 4 j p) = 0 := by
  have hz : component 3 (slice 4 j p) = 0 := by
    funext b
    apply Subtype.ext
    exact freeCoeff_blockPolynomial_of_degree_ne (component j.val p) b.val
      (by simpa only [b.property] using Ne.symm hj)
  change (rowBlockEquiv 3).symm (component 3 (slice 4 j p)) = 0
  rw [hz]
  exact (rowBlockEquiv 3).symm.map_zero

theorem rowEmbedding_projection13 (p : Forms K (3+m) 4) :
    rowEmbedding 3 (projection13 p) = slice 4 3 p := by
  change embed ((rowBlockEquiv 3) ((rowBlockEquiv 3).symm (component 3 p))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl


private theorem zeroForm_eq_C {n : ℕ} (x : Forms K n 0) : x.val = C (x.val.coeff 0) := by
  exact totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (p := x.val)).mpr x.property)

/-- All pure core forms fill exactly the zero-child-degree component. -/
theorem coreEmbed_range : LinearMap.range (SplitBlock31.coreEmbed (K := K) (m := m) (d := d)) =
    bidegreeSpace K 3 m d 0 := by
  rw [← polynomialEmbedding_range]
  apply le_antisymm
  · rintro p ⟨x, rfl⟩
    let oneY : Forms K m 0 := ⟨1, isHomogeneous_one (Fin m) K⟩
    refine ⟨x ⊗ₜ[K] oneY, ?_⟩
    apply Subtype.ext
    rw [polynomialEmbedding_tmul_val x oneY]
    simp [oneY]
  · rintro p ⟨a,rfl⟩
    induction a using TensorProduct.inductionOn with
    | tmul x y =>
      refine ⟨y.val.coeff 0 • x, ?_⟩
      apply Subtype.ext
      rw [polynomialEmbedding_tmul_val x y, SplitBlock31.coreEmbed_val, Submodule.coe_smul,
        map_smul, zeroForm_eq_C y, rename_C]
      simp [smul_eq_C_mul, mul_comm]
    | add a b ha hb => simpa only [map_add] using (LinearMap.range _).add_mem ha hb

theorem childEmbed_injective : Function.Injective (SplitBlock31.childEmbed (K := K) (m := m) (d := d)) := by
  intro p r h
  apply Subtype.ext
  exact rename_injective _ (Fin.natAdd_injective m 3) (congrArg Subtype.val h)

theorem childEmbed_range_two : LinearMap.range (SplitBlock31.childEmbed (K := K) (m := m) (d := 2)) =
    bidegreeSpace K 3 m 0 2 := by
  rw [← polynomialEmbedding_range]
  apply le_antisymm
  · rintro p ⟨y, rfl⟩
    let oneX : Forms K 3 0 := ⟨1, isHomogeneous_one (Fin 3) K⟩
    refine ⟨oneX ⊗ₜ[K] y, ?_⟩
    apply Subtype.ext
    rw [polynomialEmbedding_tmul_val oneX y]
    simp [oneX]
  · rintro p ⟨a,rfl⟩
    induction a using TensorProduct.inductionOn with
    | tmul x y =>
      refine ⟨x.val.coeff 0 • y, ?_⟩
      apply Subtype.ext
      rw [polynomialEmbedding_tmul_val x y, SplitBlock31.childEmbed_val, Submodule.coe_smul,
        map_smul, zeroForm_eq_C x, rename_C]
      simp [smul_eq_C_mul]
    | add a b ha hb => simpa only [map_add] using (LinearMap.range _).add_mem ha hb

theorem childEmbed_range_four : LinearMap.range (SplitBlock31.childEmbed (K := K) (m := m) (d := 4)) =
    bidegreeSpace K 3 m 0 4 := by
  rw [← polynomialEmbedding_range]
  apply le_antisymm
  · rintro p ⟨y, rfl⟩
    let oneX : Forms K 3 0 := ⟨1, isHomogeneous_one (Fin 3) K⟩
    refine ⟨oneX ⊗ₜ[K] y, ?_⟩
    apply Subtype.ext
    rw [polynomialEmbedding_tmul_val oneX y]
    simp [oneX]
  · rintro p ⟨a,rfl⟩
    induction a using TensorProduct.inductionOn with
    | tmul x y =>
      refine ⟨x.val.coeff 0 • y, ?_⟩
      apply Subtype.ext
      rw [polynomialEmbedding_tmul_val x y, SplitBlock31.childEmbed_val, Submodule.coe_smul,
        map_smul, zeroForm_eq_C x, rename_C]
      simp [smul_eq_C_mul]
    | add a b ha hb => simpa only [map_add] using (LinearMap.range _).add_mem ha hb

/-- Every actual quadric is a pure, mixed, and child sum. -/
theorem quadratic_decomposition (p : Forms K (3+m) 2) :
    ∃ (x : Forms K 3 2) (a : MiddleCoordinates.Mixed K m) (y : Forms K m 2),
      p = SplitBlock31.coreEmbed x + SplitBlock22.mixedEmbedding a + SplitBlock31.childEmbed y := by
  have h0 : slice 2 0 p ∈ LinearMap.range (SplitBlock31.coreEmbed (K := K) (m := m) (d := 2)) := by
    rw [coreEmbed_range]
    exact ⟨component 0 p, rfl⟩
  have h1 : slice 2 1 p ∈ LinearMap.range (rowEmbedding (K := K) (m := m) 1) := by
    rw [rowEmbedding_range]
    exact ⟨component 1 p, rfl⟩
  have h2 : slice 2 2 p ∈ LinearMap.range (SplitBlock31.childEmbed (K := K) (m := m) (d := 2)) := by
    rw [childEmbed_range_two]
    exact ⟨component 2 p, rfl⟩
  obtain ⟨x,hx⟩ := h0
  obtain ⟨a,ha⟩ := h1
  obtain ⟨y,hy⟩ := h2
  refine ⟨x,a,y,?_⟩
  rw [← rowEmbedding_one, hx, ha, hy]
  exact (sum_slices p).symm.trans (Fin.sum_univ_three (fun j => slice 2 j p))

/-- A product of represented bidegrees has no retained component at a different degree. -/
theorem projection13_zero_of_blocks {i j i' j' : ℕ}
    (u : Block K 3 m i j) (v : Block K 3 m i' j')
    (p : Forms K (3+m) 4) (hp : p.val = blockPolynomial u * blockPolynomial v)
    (hj : j+j' ≠ 3) : projection13 p = 0 := by
  have hz : component 3 p = 0 := by
    funext b
    apply Subtype.ext
    change freeCoeff b.val p.val = 0
    rw [hp]
    exact product_freeCoeff_eq_zero u v b.val (by simpa only [b.property] using Ne.symm hj)
  change (rowBlockEquiv 3).symm (component 3 p) = 0
  rw [hz]
  exact (rowBlockEquiv 3).symm.map_zero

/-- Products of arbitrary pure core quadrics have zero (1,3) projection. -/
theorem projection13_core_mul (x : Forms K 3 2) (p : Forms K (3+m) 2) :
    projection13 (mulQuadratic (SplitBlock31.coreEmbed x) p) = 0 := by
  obtain ⟨u,hu⟩ := (show SplitBlock31.coreEmbed (m := m) x ∈ bidegreeSpace K 3 m 2 0 by
    rw [← coreEmbed_range]; exact ⟨x,rfl⟩)
  obtain ⟨a,b,e,hp⟩ := quadratic_decomposition p
  rw [hp, map_add, map_add, map_add, map_add]
  have h0 : ∀ z : Forms K 3 2, projection13 (m := m) (mulQuadratic (SplitBlock31.coreEmbed x)
      (SplitBlock31.coreEmbed z)) = 0 := by
    intro z
    obtain ⟨v,hv⟩ := (show SplitBlock31.coreEmbed (m := m) z ∈ bidegreeSpace K 3 m 2 0 by
      rw [← coreEmbed_range]; exact ⟨z,rfl⟩)
    exact projection13_zero_of_blocks u v _ (by rw [← hu, ← hv]; rfl) (by decide)
  have h1 : projection13 (mulQuadratic (SplitBlock31.coreEmbed x) (SplitBlock22.mixedEmbedding b)) = 0 := by
    obtain ⟨v,hv⟩ := (show SplitBlock22.mixedEmbedding b ∈ bidegreeSpace K 3 m 1 1 by
      rw [← rowEmbedding_range]; exact ⟨b,rowEmbedding_one b⟩)
    exact projection13_zero_of_blocks u v _ (by rw [← hu, ← hv]; rfl) (by decide)
  have h2 : projection13 (mulQuadratic (SplitBlock31.coreEmbed x) (SplitBlock31.childEmbed e)) = 0 := by
    obtain ⟨v,hv⟩ := (show SplitBlock31.childEmbed e ∈ bidegreeSpace K 3 m 0 2 by
      rw [← childEmbed_range_two]; exact ⟨e,rfl⟩)
    exact projection13_zero_of_blocks u v _ (by rw [← hu, ← hv]; rfl) (by decide)
  rw [h0, h1, h2, add_zero, add_zero]


/-- The actual cubic row produced by one mixed quadric and one child quadric. -/
def rowProduct (g : MiddleCoordinates.Mixed K m) (a : Forms K m 2) : GeneralF13.Ambient K m :=
  fun i => CubicGeneric.mulLinearQuad (g i) a

/-- The (1,3) product is the literal full-ring polynomial product. -/
theorem mixed_child_product (g : MiddleCoordinates.Mixed K m) (a : Forms K m 2) :
    mulQuadratic (SplitBlock22.mixedEmbedding g) (SplitBlock31.childEmbed a) =
      rowEmbedding 3 (rowProduct g a) := by
  apply Subtype.ext
  change (SplitBlock22.mixedEmbedding g).val * (SplitBlock31.childEmbed a).val = _
  rw [SplitBlock22.mixedEmbedding_val, SplitBlock31.childEmbed_val, rowEmbedding_val, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rowProduct, CubicGeneric.mulLinearQuad_val, map_mul, mul_assoc]

theorem mulQuadratic_comm (a b : Forms K (3+m) 2) : mulQuadratic a b = mulQuadratic b a :=
  Subtype.ext (mul_comm _ _)

theorem projection13_mixed_mixed (g a : MiddleCoordinates.Mixed K m) :
    projection13 (mulQuadratic (SplitBlock22.mixedEmbedding g) (SplitBlock22.mixedEmbedding a)) = 0 := by
  have hb (x : MiddleCoordinates.Mixed K m) : SplitBlock22.mixedEmbedding x ∈ bidegreeSpace K 3 m 1 1 := by
    rw [← rowEmbedding_range]
    exact ⟨x, rowEmbedding_one x⟩
  obtain ⟨u,hu⟩ := hb g
  obtain ⟨v,hv⟩ := hb a
  exact projection13_zero_of_blocks u v _ (by rw [← hu, ← hv]; rfl) (by decide)

theorem projection13_child_child (g a : Forms K m 2) :
    projection13 (mulQuadratic (SplitBlock31.childEmbed g) (SplitBlock31.childEmbed a)) = 0 := by
  have hb (x : Forms K m 2) : SplitBlock31.childEmbed x ∈ bidegreeSpace K 3 m 0 2 := by
    rw [← childEmbed_range_two]
    exact ⟨x, rfl⟩
  obtain ⟨u,hu⟩ := hb g
  obtain ⟨v,hv⟩ := hb a
  exact projection13_zero_of_blocks u v _ (by rw [← hu, ← hv]; rfl) (by decide)

/-- Only the child-quadratic coefficient contributes for a mixed generator. -/
theorem projection13_mixed_mul (g : MiddleCoordinates.Mixed K m) (p : Forms K (3+m) 2) :
    projection13 (mulQuadratic (SplitBlock22.mixedEmbedding g) p) =
      rowProduct g (SplitBlock22.childProjection p) := by
  obtain ⟨x,a,y,rfl⟩ := quadratic_decomposition p
  rw [map_add, map_add, map_add, map_add,
    mulQuadratic_comm (SplitBlock22.mixedEmbedding g) (SplitBlock31.coreEmbed x),
    projection13_core_mul, projection13_mixed_mixed, mixed_child_product,
    projection13_rowEmbedding]
  simp

/-- Only the mixed coefficient contributes for a child generator. -/
theorem projection13_child_mul (h : Forms K m 2) (p : Forms K (3+m) 2) :
    projection13 (mulQuadratic (SplitBlock31.childEmbed h) p) =
      rowProduct (SplitBlock22.middleProjection p) h := by
  obtain ⟨x,a,y,rfl⟩ := quadratic_decomposition p
  rw [map_add, map_add, map_add, map_add,
    mulQuadratic_comm (SplitBlock31.childEmbed h) (SplitBlock31.coreEmbed x),
    projection13_core_mul,
    mulQuadratic_comm (SplitBlock31.childEmbed h) (SplitBlock22.mixedEmbedding a),
    mixed_child_product, projection13_rowEmbedding, projection13_child_child]
  simp

/-- Extract the actual source coefficients affecting bidegree (1,3). -/
def sourceProjection13 :
    (Fin (4+(c+q)) → Forms K (3+m) 2) →ₗ[K]
      (GeneralF13.CoefficientSource K m c × GeneralF13.CubicSource K m q) :=
  (LinearMap.pi fun j : Fin c => SplitBlock22.childProjection.comp
    (LinearMap.proj (Fin.natAdd 4 (Fin.castAdd q j)))).prod
  (LinearMap.pi fun k : Fin q => SplitBlock22.middleProjection.comp
    (LinearMap.proj (Fin.natAdd 4 (Fin.natAdd c k))))

/-- Projection of the full polynomial multiplication is exactly the actual combined F13 map. -/
theorem projection13_multiplication (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Fin (4+(c+q)) → Forms K (3+m) 2) :
    projection13 (quadraticMultiplication (SplitBlock22.fullGenerators g h) a) =
      GeneralF13.combined g h (sourceProjection13 a) := by
  simp only [quadraticMultiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [SplitBlock22.fullGenerators_pure, SplitBlock22.fullGenerators_mixed,
    SplitBlock22.fullGenerators_child, projection13_core_mul, projection13_mixed_mul,
    projection13_child_mul, Finset.sum_const_zero, zero_add]
  funext i
  apply Subtype.ext
  simp [GeneralF13.combined, GeneralF13.multiplication, GeneralF13.childMultiplication,
    ConvolutionF13Square.rowwise, CubicGeneric.cubicMap_val, sourceProjection13, rowProduct]


/-- Insert exactly the source terms that produce bidegree (1,3). -/
def sourceEmbedding13 :
    (GeneralF13.CoefficientSource K m c × GeneralF13.CubicSource K m q) →ₗ[K]
      (Fin (4+(c+q)) → Forms K (3+m) 2) where
  toFun a := Fin.addCases (fun _ => 0)
    (Fin.addCases (fun j => SplitBlock31.childEmbed (a.1 j))
      (fun k => SplitBlock22.mixedEmbedding (a.2 k)))
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

@[simp] theorem sourceProjection13_sourceEmbedding13
    (a : GeneralF13.CoefficientSource K m c × GeneralF13.CubicSource K m q) :
    sourceProjection13 (sourceEmbedding13 a) = a := by
  apply Prod.ext <;> funext i <;> simp [sourceProjection13, sourceEmbedding13]

/-- An actual polynomial lying in bidegree (1,3) is recovered by the retained rows. -/
theorem rowEmbedding_projection13_of_mem (p : Forms K (3+m) 4)
    (hp : p ∈ LinearMap.range (rowEmbedding (K := K) (m := m) 3)) :
    rowEmbedding 3 (projection13 p) = p := by
  obtain ⟨a,rfl⟩ := hp
  rw [projection13_rowEmbedding]

/-- The inserted source produces precisely the retained actual polynomial rows. -/
theorem multiplication_sourceEmbedding13 (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (a : GeneralF13.CoefficientSource K m c × GeneralF13.CubicSource K m q) :
    quadraticMultiplication (SplitBlock22.fullGenerators g h) (sourceEmbedding13 a) =
      rowEmbedding 3 (GeneralF13.combined g h a) := by
  have hmem : quadraticMultiplication (SplitBlock22.fullGenerators g h) (sourceEmbedding13 a) ∈
      LinearMap.range (rowEmbedding (K := K) (m := m) 3) := by
    simp only [quadraticMultiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    apply Submodule.sum_mem
    intro i _
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [sourceEmbedding13]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro k
        simp only [sourceEmbedding13, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_right, Fin.addCases_left,
          SplitBlock22.fullGenerators_mixed, mixed_child_product]
        exact ⟨rowProduct (g k) (a.1 k), rfl⟩
      · intro k
        simp only [sourceEmbedding13, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_right,
          SplitBlock22.fullGenerators_child]
        rw [mulQuadratic_comm, mixed_child_product]
        exact ⟨rowProduct (a.2 k) (h k), rfl⟩
  have hrecovery := rowEmbedding_projection13_of_mem _ hmem
  rw [projection13_multiplication, sourceProjection13_sourceEmbedding13] at hrecovery
  exact hrecovery.symm

/-- Insert only pure-child quadratic multipliers on the child generator slots. -/
def sourceEmbedding04 : (Fin q → Forms K m 2) →ₗ[K]
    (Fin (4+(c+q)) → Forms K (3+m) 2) where
  toFun a := Fin.addCases (fun _ => 0) (Fin.addCases (fun _ => 0)
    (fun k => SplitBlock31.childEmbed (a k)))
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

theorem multiplication_sourceEmbedding04 (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : Fin q → Forms K m 2) :
    quadraticMultiplication (SplitBlock22.fullGenerators g h) (sourceEmbedding04 a) =
      SplitBlock31.childEmbed (quadraticMultiplication h a) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val, SplitBlock31.childEmbed_val, quadraticMultiplication_val]
  simp only [Fin.sum_univ_add, sourceEmbedding04, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_left, Fin.addCases_right,
    SplitBlock22.fullGenerators_child, Submodule.coe_zero, mul_zero, Finset.sum_const_zero,
    zero_add, SplitBlock31.childEmbed_val, map_sum, map_mul]

theorem target31_le_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) :
    bidegreeSpace K 3 m 3 1 ≤ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range := by
  rw [← SplitBlock31.range_linearYEmbed]
  rintro p ⟨a,rfl⟩
  obtain ⟨b,rfl⟩ := SplitMiddle31.multiplication_surjective (fun j => SplitBlock22.traceCoordinates (g j)) a
  exact ⟨SplitBlock31.sourceEmbedding b,
    SplitBlock31.multiplication_commutes (fun j => SplitBlock22.traceCoordinates (g j)) h b⟩

theorem target04_le_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hh : Function.Surjective (quadraticMultiplication h)) :
    bidegreeSpace K 3 m 0 4 ≤ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range := by
  rw [← childEmbed_range_four]
  rintro p ⟨a,rfl⟩
  obtain ⟨b,rfl⟩ := hh a
  exact ⟨sourceEmbedding04 b,multiplication_sourceEmbedding04 g h b⟩

/-- Every discarded target component lies in the actual split multiplication image. -/
theorem kernel_projection13_le_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h)) :
    (projection13 (K := K) (m := m)).ker ≤ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range := by
  intro p hp
  rw [← sum_slices p]
  apply Submodule.sum_mem
  intro j _
  fin_cases j
  · apply SplitBlock40.pure_target_le_range (fun k => SplitBlock22.traceCoordinates (g k)) h
    rw [coreEmbed_range]
    exact ⟨component 0 p,rfl⟩
  · exact target31_le_range g h ⟨component 1 p,rfl⟩
  · exact SplitBlock22.full_target_le_range g h h22 ⟨component 2 p,rfl⟩
  · have hz : slice 4 3 p = 0 := by
      rw [← rowEmbedding_projection13, show projection13 p = 0 from hp]
      exact (rowEmbedding 3).map_zero
    change slice 4 (3 : Fin 5) p ∈ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range
    rw [hz]
    exact Submodule.zero_mem _
  · exact target04_le_range g h h04 ⟨component 4 p,rfl⟩


/-- The exact full image is the preimage of the retained (1,3) multiplication image. -/
theorem fullImage_eq_comap (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h)) :
    (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range =
      (GeneralF13.combined g h).range.comap projection13 := by
  apply le_antisymm
  · rintro p ⟨a,rfl⟩
    exact ⟨sourceProjection13 a, (projection13_multiplication g h a).symm⟩
  · intro p hp
    obtain ⟨a,ha⟩ := hp
    let z := quadraticMultiplication (SplitBlock22.fullGenerators g h) (sourceEmbedding13 a)
    have hz : z ∈ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range :=
      ⟨sourceEmbedding13 a,rfl⟩
    have hker : p-z ∈ (projection13 (K := K) (m := m)).ker := by
      change projection13 (p-z) = 0
      rw [map_sub]
      change projection13 p - projection13 (quadraticMultiplication _ (sourceEmbedding13 a)) = 0
      rw [projection13_multiplication, sourceProjection13_sourceEmbedding13, ha, sub_self]
    have hmem := (LinearMap.range _).add_mem (kernel_projection13_le_range g h h22 h04 hker) hz
    simpa only [sub_add_cancel] using hmem

private def quotientTransport {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (A : Submodule K V) (B : Submodule K W)
    (hA : A = B.comap f) (hs : Function.Surjective f) : (V ⧸ A) ≃ₗ[K] (W ⧸ B) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ]; exact hA)).trans
    ((B.mkQ.comp f).quotKerEquivOfSurjective (B.mkQ_surjective.comp hs))

abbrev Cokernel (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :=
  Forms K (3+m) 4 ⧸ (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range

abbrev RawJ (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :=
  GeneralF13.Ambient K m ⧸ (GeneralF13.combined g h).range

/-- The full actual cokernel is precisely the quotient of the retained cubic rows. -/
def cokernelEquivRawJ (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h)) :
    Cokernel g h ≃ₗ[K] RawJ g h :=
  quotientTransport projection13 _ _ (fullImage_eq_comap g h h22 h04) projection13_surjective

/-- Every tuple of cubic quotient classes has a tuple of actual cubic representatives. -/
theorem f13TargetProjection_surjective (h : Fin q → Forms K m 2) :
    Function.Surjective (GeneralF13.targetProjection h) := by
  classical
  intro u
  choose a ha using fun i => (CubicGeneric.quadraticLinearProducts h).mkQ_surjective (u i)
  exact ⟨a,funext ha⟩

theorem combinedImage_eq_comap (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) :
    (GeneralF13.combined g h).range =
      (GeneralF13.f13Map g h).range.comap (GeneralF13.targetProjection h) := by
  rw [GeneralF13.f13Map_range]
  apply le_antisymm
  · rintro p ⟨⟨a,b⟩,rfl⟩
    refine ⟨a,?_⟩
    change GeneralF13.targetProjection h (GeneralF13.multiplication g a) =
      GeneralF13.targetProjection h (GeneralF13.multiplication g a + GeneralF13.childMultiplication h b)
    rw [map_add]
    have hz : GeneralF13.targetProjection h (GeneralF13.childMultiplication h b) = 0 := by
      have hb : GeneralF13.childMultiplication h b ∈ (GeneralF13.targetProjection h).ker := by
        rw [GeneralF13.targetProjection_kernel]
        exact ⟨b,rfl⟩
      exact hb
    rw [hz, add_zero]
  · intro p hp
    obtain ⟨a,ha⟩ := hp
    have hker : p - GeneralF13.multiplication g a ∈ (GeneralF13.targetProjection h).ker := by
      change GeneralF13.targetProjection h (p - GeneralF13.multiplication g a) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr ha.symm
    rw [GeneralF13.targetProjection_kernel] at hker
    obtain ⟨b,hb⟩ := hker
    refine ⟨(a,b),?_⟩
    change GeneralF13.multiplication g a + GeneralF13.childMultiplication h b = p
    rw [hb]
    abel

/-- The ordinary-quotient outer cokernel J. -/
abbrev J (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :=
  GeneralF13.Target h ⧸ (GeneralF13.f13Map g h).range

/-- The raw rows and the ordinary child quotient construction give the same actual J. -/
def rawJEquivJ (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    RawJ g h ≃ₗ[K] J g h :=
  quotientTransport (GeneralF13.targetProjection h) _ _ (combinedImage_eq_comap g h)
    (f13TargetProjection_surjective h)

/-- Canonical actual full split cokernel identification; no source homology exhaustion is assumed. -/
def cokernelEquivJ (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h)) :
    Cokernel g h ≃ₗ[K] J g h :=
  (cokernelEquivRawJ g h h22 h04).trans (rawJEquivJ g h)

/-- The actual polynomial projection to the surviving split cokernel. -/
def projectionJ (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    Forms K (3+m) 4 →ₗ[K] J g h :=
  (GeneralF13.f13Map g h).range.mkQ.comp ((GeneralF13.targetProjection h).comp projection13)

theorem projectionJ_surjective (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    Function.Surjective (projectionJ g h) :=
  (GeneralF13.f13Map g h).range.mkQ_surjective.comp
    ((f13TargetProjection_surjective h).comp projection13_surjective)

/-- Exact kernel identity for the concrete polynomial-to-J projection. -/
theorem projectionJ_ker (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h)) :
    (projectionJ g h).ker = (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range := by
  rw [projectionJ, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_comp,
    ← combinedImage_eq_comap, ← fullImage_eq_comap g h h22 h04]

@[simp] theorem projectionJ_rowEmbedding (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : GeneralF13.Ambient K m) :
    projectionJ g h (rowEmbedding 3 a) =
      (GeneralF13.f13Map g h).range.mkQ (GeneralF13.targetProjection h a) := by
  simp [projectionJ]

@[simp] theorem cokernelEquivJ_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h)) (p : Forms K (3+m) 4) :
    cokernelEquivJ g h h22 h04 (Submodule.Quotient.mk p) = projectionJ g h p := by
  simp [cokernelEquivJ, cokernelEquivRawJ, rawJEquivJ, quotientTransport, projectionJ]

/-- The actual outer quotient dimension on the independent cubic/F13 locus. -/
theorem rawJ_finrank_eq_j (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (hlin : LinearIndependent K h)
    (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h)) :
    (finrank K (RawJ g h) : ℤ) = Counts.j m q c := by
  have hq : q ≤ (m+1).choose 2 := by
    have ht := (Submodule.span K (Set.range h)).finrank_quotient_add_finrank
    rw [finrank_span_eq_card hlin, Fintype.card_fin, finrank_quadrics] at ht
    omega
  have hr := GeneralF13.combined_rank g h
  rw [LinearMap.finrank_range_of_inj h13, GeneralF13.source_finrank h hlin,
    GeneralF13.childMultiplication_finrank h hcubic] at hr
  have hquot := (GeneralF13.combined g h).range.finrank_quotient_add_finrank
  have hamb : finrank K (GeneralF13.Ambient K m) = 3 * (m+2).choose 3 := by
    let : Module.Free K (Forms K m 3) := Module.Free.of_basis (formsBasis K m 3)
    simp [GeneralF13.Ambient, Module.finrank_pi_fintype, finrank_forms]
  rw [hamb, ← hr] at hquot
  change finrank K (RawJ g h) + (c*((m+1).choose 2-q)+3*m*q) = 3*(m+2).choose 3 at hquot
  have hi := congrArg (fun n : ℕ => (n : ℤ)) hquot
  push_cast [Nat.cast_sub hq] at hi
  unfold Counts.j Counts.beta Counts.alpha Counts.b2 Counts.b3
  linarith

/-- Dimension of the genuine full quartic cokernel, derived from the actual quotient equivalence. -/
theorem cokernel_finrank_eq_j (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h))
    (hlin : LinearIndependent K h) (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h)) :
    (finrank K (Cokernel g h) : ℤ) = Counts.j m q c := by
  rw [(cokernelEquivRawJ g h h22 h04).finrank_eq]
  exact rawJ_finrank_eq_j g h hlin hcubic h13

/-- The actual split rank used by the narrower deformation-minor argument. -/
theorem split_rank_eq (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (h22 : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (h04 : Function.Surjective (quadraticMultiplication h))
    (hlin : LinearIndependent K h) (hcubic : Function.Injective (CubicGeneric.cubicMap h))
    (h13 : Function.Injective (GeneralF13.f13Map g h)) :
    (finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range : ℤ) =
      Counts.b4 (3+m) - Counts.j m q c := by
  have hr := (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range.finrank_quotient_add_finrank
  rw [finrank_quartics] at hr
  change finrank K (Cokernel g h) + finrank K (quadraticMultiplication (SplitBlock22.fullGenerators g h)).range = _ at hr
  have hi := congrArg (fun n : ℕ => (n : ℤ)) hr
  push_cast at hi
  rw [cokernel_finrank_eq_j g h h22 h04 hlin hcubic h13] at hi
  unfold Counts.b4
  omega

end Quartic.ActualSplitCokernel
