import Quartic.SplitTensor
import Quartic.ThreeBlockQuotient
import Quartic.MiddleCoordinates

/-!
# Actual elimination in the (2,2) polynomial block

The target is the tensor product of the actual pure and child quadratic
polynomial spaces, faithfully embedded into the full quartic polynomials.
Eliminating the pure four-quadric relations and the child relations gives
exactly two copies of the child quadratic quotient. The two eliminated
images intersect in exactly the pure–child tensor relations.
-/
noncomputable section
namespace Quartic.SplitBlock22
open Module MvPolynomial ThreeBlockQuotient ThreeBlockModel
open scoped TensorProduct
variable {K : Type*} [Field K] {m c q : ℕ}

abbrev Target (K : Type*) [Field K] (m : ℕ) := Forms K 3 2 ⊗[K] Forms K m 2

/-- The actual quartic-polynomial embedding of the target. -/
def targetEmbedding : Target K m →ₗ[K] Forms K (3 + m) 4 :=
  SplitTensor.polynomialEmbedding

theorem targetEmbedding_injective : Function.Injective
    (targetEmbedding (K := K) (m := m)) := SplitTensor.polynomialEmbedding_injective

theorem targetEmbedding_range : LinearMap.range (targetEmbedding (K := K) (m := m)) =
    SplitBigrading.bidegreeSpace K 3 m 2 2 := SplitTensor.polynomialEmbedding_range

@[simp] theorem targetEmbedding_tmul_val (x : Forms K 3 2) (y : Forms K m 2) :
    (targetEmbedding (x ⊗ₜ[K] y)).val =
      rename (Fin.castAdd m) x.val * rename (Fin.natAdd 3) y.val :=
  SplitTensor.polynomialEmbedding_tmul_val x y

/-- Products of the four pure relations by arbitrary child quadrics. -/
def pureImage : Submodule K (Target K m) := SplitTensor.leftRelations pureSpace

/-- Products of arbitrary pure quadrics by a child relation. -/
def childImage (Q : Submodule K (Forms K m 2)) : Submodule K (Target K m) :=
  SplitTensor.rightRelations Q

/-- The pure–child overlap, before embedding in the actual polynomials. -/
def crossImage (Q : Submodule K (Forms K m 2)) : Submodule K (Target K m) :=
  SplitTensor.jointRelations pureSpace Q

private def pairTensor (A : Type*) [AddCommGroup A] [Module K A] :
    ((K × K) ⊗[K] A) ≃ₗ[K] A × A :=
  (TensorProduct.prodLeft K K K K A).trans
    ((TensorProduct.lid K A).prodCongr (TensorProduct.lid K A))

@[simp] private theorem pairTensor_tmul {A : Type*} [AddCommGroup A] [Module K A]
    (a : K × K) (x : A) : pairTensor A (a ⊗ₜ[K] x) = (a.1 • x, a.2 • x) := by
  rcases a with ⟨a,b⟩
  simp [pairTensor]

/-- The genuine pure quotient tensor the genuine child quotient, in two coordinates. -/
def quotientCoordinates (Q : Submodule K (Forms K m 2)) :
    (PureQuotient K ⊗[K] (Forms K m 2 ⧸ Q)) ≃ₗ[K]
      (Forms K m 2 ⧸ Q) × (Forms K m 2 ⧸ Q) :=
  (TensorProduct.congr quotientEquiv (LinearEquiv.refl K _)).trans (pairTensor _)

/-- Eliminate both actual quadratic relation spaces from bidegree (2,2). -/
def elimination (Q : Submodule K (Forms K m 2)) :
    Target K m →ₗ[K] (Forms K m 2 ⧸ Q) × (Forms K m 2 ⧸ Q) :=
  (quotientCoordinates Q).toLinearMap.comp (TensorProduct.map pureSpace.mkQ Q.mkQ)

@[simp] theorem elimination_tmul (Q : Submodule K (Forms K m 2))
    (x : Forms K 3 2) (y : Forms K m 2) :
    elimination Q (x ⊗ₜ[K] y) = ((reduction x).1 • Q.mkQ y, (reduction x).2 • Q.mkQ y) := by
  simp [elimination, quotientCoordinates]

/-- Elimination is onto the actual two-coordinate quotient target. -/
theorem elimination_surjective (Q : Submodule K (Forms K m 2)) :
    Function.Surjective (elimination Q) :=
  (quotientCoordinates Q).surjective.comp
    (TensorProduct.map_surjective pureSpace.mkQ_surjective Q.mkQ_surjective)

/-- No additional relation is lost by the two-coordinate elimination. -/
theorem elimination_ker (Q : Submodule K (Forms K m 2)) :
    (elimination Q).ker = pureImage ⊔ childImage Q := by
  rw [elimination, LinearMap.ker_comp_of_ker_eq_bot _ (quotientCoordinates Q).ker]
  exact SplitTensor.quotient_kernel pureSpace Q

/-- The overlap consists exactly of pure–child cross products. -/
theorem pureImage_inf_childImage (Q : Submodule K (Forms K m 2)) :
    pureImage ⊓ childImage Q = crossImage Q :=
  SplitTensor.relations_intersection pureSpace Q

/-- The same exact overlap identity holds inside the actual full quartic space. -/
theorem actual_images_intersection (Q : Submodule K (Forms K m 2)) :
    pureImage.map targetEmbedding ⊓ (childImage Q).map targetEmbedding =
      (crossImage Q).map targetEmbedding := by
  rw [← Submodule.map_inf _ targetEmbedding_injective]
  rw [pureImage_inf_childImage]

/-- Actual multiplication by the four pure quadrics in this block. -/
def pureMap : (Fin 4 → Forms K m 2) →ₗ[K] Target K m :=
  SplitTensor.sumTensorLeft blockQuadrics

/-- Actual multiplication by the chosen child quadrics in this block. -/
def childMap (h : Fin q → Forms K m 2) : (Fin q → Forms K 3 2) →ₗ[K] Target K m :=
  SplitTensor.sumTensorRight h

@[simp] theorem pureMap_apply (a : Fin 4 → Forms K m 2) :
    pureMap a = ∑ i, blockQuadrics i ⊗ₜ[K] a i := SplitTensor.sumTensorLeft_apply _ _

@[simp] theorem childMap_apply (h : Fin q → Forms K m 2) (a : Fin q → Forms K 3 2) :
    childMap h a = ∑ i, a i ⊗ₜ[K] h i := SplitTensor.sumTensorRight_apply _ _

theorem pureMap_range : LinearMap.range (pureMap (K := K) (m := m)) = pureImage :=
  SplitTensor.sumTensorLeft_range _

theorem childMap_range (h : Fin q → Forms K m 2) :
    LinearMap.range (childMap h) = childImage (Submodule.span K (Set.range h)) :=
  SplitTensor.sumTensorRight_range _

/-- Kernel identity stated using the actual coefficient multiplication maps. -/
theorem elimination_ker_ranges (h : Fin q → Forms K m 2) :
    (elimination (Submodule.span K (Set.range h))).ker =
      LinearMap.range pureMap ⊔ LinearMap.range (childMap h) := by
  rw [pureMap_range, childMap_range, elimination_ker]

/-- The pure–child overlap is spanned by the actual generator pair products. -/
theorem crossImage_span (h : Fin q → Forms K m 2) :
    crossImage (Submodule.span K (Set.range h)) =
      Submodule.span K (Set.range (fun p : Fin 4 × Fin q => blockQuadrics p.1 ⊗ₜ[K] h p.2)) := by
  unfold crossImage SplitTensor.jointRelations
  rw [TensorProduct.range_map, Submodule.range_subtype, Submodule.range_subtype]
  rw [pureSpace, Submodule.map₂_span_span]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
    exact ⟨(i,j), rfl⟩
  · rintro ⟨⟨i,j⟩, rfl⟩
    exact ⟨blockQuadrics i, ⟨i, rfl⟩, h j, ⟨j, rfl⟩, rfl⟩

private theorem joint_finrank {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K X] [FiniteDimensional K Y]
    (P : Submodule K X) (Q : Submodule K Y) :
    finrank K (SplitTensor.jointRelations P Q) = finrank K P * finrank K Q := by
  unfold SplitTensor.jointRelations
  rw [LinearMap.finrank_range_of_inj
    (TensorProduct.map_injective_of_flat_flat _ _ P.subtype_injective Q.subtype_injective)]
  exact Module.finrank_tensorProduct

/-- The exact dimension of the overlap, with no chosen child basis required. -/
theorem crossImage_finrank (Q : Submodule K (Forms K m 2)) :
    finrank K (crossImage Q) = 4 * finrank K Q := by
  rw [crossImage, joint_finrank, pureSpace_finrank]

/-- For independent child generators, there are exactly `4q` pure–child overlaps. -/
theorem crossImage_finrank_of_independent (h : Fin q → Forms K m 2)
    (hh : LinearIndependent K h) :
    finrank K (crossImage (Submodule.span K (Set.range h))) = 4 * q := by
  rw [crossImage_finrank, finrank_span_eq_card hh, Fintype.card_fin]

/-- A product of two actual pure coordinate linear forms. -/
def variableProduct (i j : Fin 3) : Forms K 3 2 :=
  ⟨X i * X j, (isHomogeneous_X K i).mul (isHomogeneous_X K j)⟩

set_option maxRecDepth 4096 in
@[simp] theorem reduction_variableProduct (i j : Fin 3) :
    reduction (variableProduct (K := K) i j) =
      if i = j then if i = 0 then (1,0) else if i = 1 then (0,1) else (-1,-1) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction, variableProduct, lcoeff, MvPolynomial.X,
      monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]

/-- The actual mixed-by-mixed product in the biform target. -/
def mixedProduct (g : MiddleCoordinates.Mixed K m) :
    MiddleCoordinates.Mixed K m →ₗ[K] Target K m :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (TensorProduct.mk K (Forms K 3 2) (Forms K m 2) (variableProduct i j)).comp
      ((MiddleCoordinates.mulLinear (g i)).comp (LinearMap.proj j))

@[simp] theorem mixedProduct_apply (g a : MiddleCoordinates.Mixed K m) :
    mixedProduct g a = ∑ i : Fin 3, ∑ j : Fin 3,
      variableProduct i j ⊗ₜ[K] MiddleCoordinates.mulLinear (g i) (a j) := by
  simp [mixedProduct]

/-- The eliminated actual product is precisely the manuscript's middle map. -/
theorem elimination_mixedProduct (Q : Submodule K (Forms K m 2))
    (g a : MiddleCoordinates.Mixed K m) :
    elimination Q (mixedProduct g a) =
      (Q.mkQ.prodMap Q.mkQ) (MiddleCoordinates.projectedProduct g a) := by
  simp [mixedProduct_apply, Fin.sum_univ_succ,
    MiddleCoordinates.projectedProduct, sub_eq_add_neg]

/-- Actual multiplication of a full mixed coefficient array. -/
def mixedMap (g : Fin c → MiddleCoordinates.Mixed K m) :
    (Fin c → MiddleCoordinates.Mixed K m) →ₗ[K] Target K m :=
  ∑ i, (mixedProduct (g i)).comp (LinearMap.proj i)

/-- The source middle quotient map is obtained by eliminating actual polynomial relations. -/
theorem elimination_mixedMap (Q : Submodule K (Forms K m 2))
    (g : Fin c → MiddleCoordinates.Mixed K m) (a : Fin c → MiddleCoordinates.Mixed K m) :
    elimination Q (mixedMap g a) = MiddleCoordinates.quotientMap g Q a := by
  simp only [mixedMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    map_sum, elimination_mixedProduct]
  simp [MiddleCoordinates.quotientMap, MiddleCoordinates.multiplication, map_sum]

/-- The actual polynomial with one X variable and one child linear form in each term. -/
def mixedEmbedding : MiddleCoordinates.Mixed K m →ₗ[K] Forms K (3 + m) 2 :=
  SplitTensor.polynomialEmbedding.comp
    (SplitTensor.sumTensorLeft (fun i : Fin 3 => (⟨X i, isHomogeneous_X K i⟩ : Forms K 3 1)))

@[simp] theorem mixedEmbedding_val (g : MiddleCoordinates.Mixed K m) :
    (mixedEmbedding g).val = ∑ i : Fin 3,
      X (Fin.castAdd m i) * rename (Fin.natAdd 3) (g i).val := by
  change (SplitTensor.polynomialEmbedding
    (SplitTensor.sumTensorLeft (fun i : Fin 3 =>
      (⟨X i, isHomogeneous_X K i⟩ : Forms K 3 1)) g)).val = _
  rw [SplitTensor.sumTensorLeft_apply, map_sum, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [SplitTensor.polynomialEmbedding_tmul_val, rename_X]

/-- The unreduced mixed product is the product of the actual mixed quadrics. -/
theorem mixedProduct_polynomial (g a : MiddleCoordinates.Mixed K m) :
    (targetEmbedding (mixedProduct g a)).val = (mixedEmbedding g).val * (mixedEmbedding a).val := by
  simp only [mixedProduct_apply, map_sum, Submodule.coe_sum, targetEmbedding_tmul_val,
    mixedEmbedding_val, variableProduct, MiddleCoordinates.mulLinear, map_mul, rename_X]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (X (Fin.castAdd m i) * X (Fin.castAdd m j)) *
    rename (Fin.natAdd 3) ((g i).val * (a j).val) = _
  rw [map_mul]
  ring

/-- A middle coefficient tuple lifts to a true bidegree cycle exactly when its quotient product vanishes. -/
theorem cycle_completion_iff (h : Fin q → Forms K m 2)
    (g : Fin c → MiddleCoordinates.Mixed K m) (a : Fin c → MiddleCoordinates.Mixed K m) :
    (∃ b : Fin 4 → Forms K m 2, ∃ d : Fin q → Forms K 3 2,
      pureMap b + mixedMap g a + childMap h d = 0) ↔
    MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) a = 0 := by
  let Q := Submodule.span K (Set.range h)
  have hp (b : Fin 4 → Forms K m 2) : elimination Q (pureMap b) = 0 := by
    have hm : pureMap b ∈ (elimination Q).ker := by
      rw [elimination_ker_ranges]
      exact Submodule.mem_sup_left ⟨b, rfl⟩
    exact hm
  have hc (d : Fin q → Forms K 3 2) : elimination Q (childMap h d) = 0 := by
    have hm : childMap h d ∈ (elimination Q).ker := by
      rw [elimination_ker_ranges]
      exact Submodule.mem_sup_right ⟨d, rfl⟩
    exact hm
  constructor
  · rintro ⟨b, d, hd⟩
    have he := congrArg (elimination Q) hd
    simpa only [map_add, hp, hc, map_zero, zero_add, add_zero, elimination_mixedMap] using he
  · intro ha
    have hm : mixedMap g a ∈ (elimination Q).ker := by
      change elimination Q (mixedMap g a) = 0
      exact (elimination_mixedMap Q g a).trans ha
    rw [elimination_ker_ranges, Submodule.mem_sup] at hm
    obtain ⟨u, ⟨b, rfl⟩, v, ⟨d, rfl⟩, he⟩ := hm
    refine ⟨-b, -d, ?_⟩
    rw [map_neg, map_neg, ← he]
    abel

/-- The actual (2,2) multiplication map before either family of relations is eliminated. -/
def multiplication (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    ((Fin 4 → Forms K m 2) × (Fin c → MiddleCoordinates.Mixed K m) ×
      (Fin q → Forms K 3 2)) →ₗ[K] Target K m :=
  pureMap.coprod ((mixedMap g).coprod (childMap h))

/-- Surjectivity of the actual middle quotient fills the actual entire (2,2) target. -/
theorem multiplication_surjective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2)
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    Function.Surjective (multiplication g h) := by
  intro z
  let Q := Submodule.span K (Set.range h)
  obtain ⟨a, ha⟩ := hs (elimination Q z)
  have hz : z - mixedMap g a ∈ (elimination Q).ker := by
    change elimination Q (z - mixedMap g a) = 0
    rw [map_sub, elimination_mixedMap, ha, sub_self]
  rw [elimination_ker_ranges, Submodule.mem_sup] at hz
  obtain ⟨u, ⟨b, rfl⟩, v, ⟨d, rfl⟩, he⟩ := hz
  refine ⟨(b,a,d), ?_⟩
  change pureMap b + (mixedMap g a + childMap h d) = z
  have he' : pureMap b + childMap h d = z - mixedMap g a := he
  rw [← sub_add_cancel z (mixedMap g a), ← he']
  abel

end Quartic.SplitBlock22
