module

public import Quartic.ActualSplitCokernel
public import Quartic.MovingMiddleCorrection
public import Quartic.RowMultiplicationCoordinates
public import Quartic.Deformation
public import Quartic.ActualDeformationResponse

@[expose] public section

/-!
# Actual deformation columns

The split quartic multiplication family is perturbed by literal pure, mixed,
and marked-child quadratic motions. Actual trace cycles give order-one
columns; actual correction classes give corrected columns with an exact
order-two response in the retained cokernel. The marked representative
condition is proved for the canonical image of actual child-cycle
coefficients. No numerical rank or homology-inventory premise is assumed.
-/
noncomputable section
namespace Quartic.ActualDeformationColumns
open Module MvPolynomial ActualSplitCokernel
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K] {m c q : ℕ}

/-- Actual quadratic motions: child quadrics on pure/mixed slots and pure quadrics on child slots. -/
def motionFamily (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) : Fin (4+(c+q)) → Forms K (3+m) 2 :=
  Fin.addCases (fun i => SplitBlock31.childEmbed (r i))
    (Fin.addCases (fun j => SplitBlock31.childEmbed (p j)) (fun k => SplitBlock31.coreEmbed (s k)))

/-- The literal perturbed family of actual quadrics. -/
def deformedFamily (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (s : Fin q → Forms K 3 2) (ε : K) :
    Fin (4+(c+q)) → Forms K (3+m) 2 :=
  SplitBlock22.fullGenerators g h + ε • motionFamily p r s

theorem quadraticMultiplication_add_smul {n t : ℕ} (f v : Fin t → Forms K n 2) (ε : K) :
    quadraticMultiplication (f + ε • v) = quadraticMultiplication f + ε • quadraticMultiplication v := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp only [quadraticMultiplication_val, Pi.add_apply, Pi.smul_apply, Submodule.coe_add,
    Submodule.coe_smul, LinearMap.add_apply, LinearMap.smul_apply, add_mul, smul_mul_assoc,
    Finset.sum_add_distrib, Finset.smul_sum]

/-- No matrix-family premise: the actual perturbed multiplication is affine linear. -/
theorem deformed_multiplication (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (s : Fin q → Forms K 3 2) (ε : K) :
    quadraticMultiplication (deformedFamily g h p r s ε) =
      quadraticMultiplication (SplitBlock22.fullGenerators g h) + ε • quadraticMultiplication (motionFamily p r s) :=
  quadraticMultiplication_add_smul _ _ ε

/-- The actual fixed ambient projection used by the deformation response. -/
def projectionRawJ (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2) :
    Forms K (3+m) 4 →ₗ[K] RawJ g h :=
  (GeneralF13.combined g h).range.mkQ.comp projection13

@[simp] theorem projectionRawJ_rowEmbedding (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (a : GeneralF13.Ambient K m) :
    projectionRawJ g h (rowEmbedding 3 a) = (GeneralF13.combined g h).range.mkQ a := by
  simp [projectionRawJ]

theorem rowProduct_eq_multiplication (a : MiddleCoordinates.Mixed K m) (p : Forms K m 2) :
    rowProduct a p = RowMultiplicationCoordinates.multiplication p a := by
  funext i
  apply Subtype.ext
  exact mul_comm _ _

/-- Actual first variation on every complete middle-block source, including its pure/child corrections. -/
theorem firstVariation_middle (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) (a : SplitBlock22.Source K m c q) :
    projection13 (quadraticMultiplication (motionFamily p r s) (SplitBlock22.sourceEmbedding a)) =
      ∑ j, RowMultiplicationCoordinates.multiplication (p j) (a.2.1 j) := by
  simp only [quadraticMultiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [motionFamily, Fin.addCases_left, Fin.addCases_right,
    SplitBlock22.sourceEmbedding_pure, SplitBlock22.sourceEmbedding_mixed, SplitBlock22.sourceEmbedding_child,
    projection13_child_mul, SplitBlock22.middleProjection_childEmbed,
    SplitBlock22.middleProjection_mixedEmbedding, map_zero,
    projection13_core_mul, rowProduct_eq_multiplication, Finset.sum_const_zero, zero_add, add_zero]

/-- Reorient a true mixed polynomial's child-first coefficients back to its three rows. -/
def traceRows : (Fin m → Forms K 3 1) →ₗ[K] MiddleCoordinates.Mixed K m :=
  SplitBlock22.middleProjection.comp SplitBlock31.linearYEmbed

/-- Actual first variation on every complete (3,1) source. -/
theorem firstVariation_trace (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) (a : SplitMiddle31.Source K m c) :
    projection13 (quadraticMultiplication (motionFamily p r s) (SplitBlock31.sourceEmbedding a)) =
      ∑ i, RowMultiplicationCoordinates.multiplication (r i) (traceRows (a.2 i)) := by
  simp only [quadraticMultiplication, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [motionFamily, Fin.addCases_left, Fin.addCases_right,
    SplitBlock31.sourceEmbedding_pure, SplitBlock31.sourceEmbedding_mixed, SplitBlock31.sourceEmbedding_child,
    projection13_child_mul, SplitBlock22.middleProjection_coreEmbed,
    rowProduct_eq_multiplication, map_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- First-order columns are actual cycles embedded in the full indexed polynomial source. -/
theorem middle_first_order (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (s : Fin q → Forms K 3 2)
    (a : SplitBlock22.Source K m c q) (ha : SplitBlock22.multiplication g h a = 0) (ε : K) :
    quadraticMultiplication (deformedFamily g h p r s ε) (SplitBlock22.sourceEmbedding a) =
      ε • quadraticMultiplication (motionFamily p r s) (SplitBlock22.sourceEmbedding a) := by
  rw [deformed_multiplication]
  apply deformation_first_response
  rw [SplitBlock22.full_multiplication_commutes, ha, map_zero]

/-- The complete trace cycle gives its literal order-one polynomial column. -/
theorem trace_first_order (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (s : Fin q → Forms K 3 2)
    (a : SplitMiddle31.Source K m c)
    (ha : SplitMiddle31.multiplication (fun j => SplitBlock22.traceCoordinates (g j)) a = 0) (ε : K) :
    quadraticMultiplication (deformedFamily g h p r s ε) (SplitBlock31.sourceEmbedding a) =
      ε • quadraticMultiplication (motionFamily p r s) (SplitBlock31.sourceEmbedding a) := by
  rw [deformed_multiplication]
  apply deformation_first_response
  change quadraticMultiplication (SplitBlock31.generators (fun j => SplitBlock22.traceCoordinates (g j)) h)
    (SplitBlock31.sourceEmbedding a) = 0
  rw [SplitBlock31.multiplication_commutes, ha, map_zero]

/-- The unreduced (2,2) first response of an actual pure quartic source. -/
def pureFirstResponse (r : Fin 4 → Forms K m 2) (a : Fin 4 → Forms K 3 2) : SplitBlock22.Target K m :=
  ∑ i, a i ⊗ₜ[K] r i

/-- Pure sources first respond by the actual pure-coefficient tensor, before elimination. -/
theorem firstVariation_pure (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) (a : Fin 4 → Forms K 3 2) :
    quadraticMultiplication (motionFamily p r s) (SplitBlock40.sourceEmbedding a) =
      SplitBlock22.targetEmbedding (pureFirstResponse r a) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val]
  simp only [Fin.sum_univ_add, motionFamily, Fin.addCases_left, Fin.addCases_right,
    SplitBlock40.sourceEmbedding_pure, SplitBlock40.sourceEmbedding_other,
    SplitBlock31.coreEmbed_val, SplitBlock31.childEmbed_val,
    Submodule.coe_zero, mul_zero, Finset.sum_const_zero, add_zero,
    pureFirstResponse, map_sum, Submodule.coe_sum, SplitBlock22.targetEmbedding_tmul_val]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The unreduced (2,2) first response of a child quartic source. -/
def childFirstResponse (s : Fin q → Forms K 3 2) (a : Fin q → Forms K m 2) : SplitBlock22.Target K m :=
  ∑ i, s i ⊗ₜ[K] a i

/-- Child cycles also have a literal bidegree-(2,2) first response. -/
theorem firstVariation_child (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) (a : Fin q → Forms K m 2) :
    quadraticMultiplication (motionFamily p r s) (sourceEmbedding04 (c := c) a) =
      SplitBlock22.targetEmbedding (childFirstResponse s a) := by
  apply Subtype.ext
  rw [quadraticMultiplication_val]
  simp [sourceEmbedding04, motionFamily, Fin.sum_univ_add, SplitBlock31.childEmbed_val,
    SplitBlock31.coreEmbed_val, childFirstResponse, SplitBlock22.targetEmbedding_tmul_val]


/-- Complete any prescribed mixed coefficient vector whose actual quotient product matches the target. -/
theorem prescribed_middle_completion (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (t : SplitBlock22.Target K m)
    (z : Fin c → MiddleCoordinates.Mixed K m)
    (hz : MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z =
      -SplitBlock22.elimination (Submodule.span K (Set.range h)) t) :
    ∃ b : SplitBlock22.Source K m c q,
      b.2.1 = z ∧ SplitBlock22.multiplication g h b = -t := by
  have hm : -t - SplitBlock22.mixedMap g z ∈
      (SplitBlock22.elimination (Submodule.span K (Set.range h))).ker := by
    change SplitBlock22.elimination _ (-t - SplitBlock22.mixedMap g z) = 0
    rw [map_sub]
    rw [← neg_one_smul K t, map_smul, neg_one_smul]
    rw [SplitBlock22.elimination_mixedMap, hz, sub_self]
  rw [SplitBlock22.elimination_ker_ranges, Submodule.mem_sup] at hm
  obtain ⟨u, ⟨a, rfl⟩, v, ⟨d, rfl⟩, he⟩ := hm
  refine ⟨(a,z,d),rfl,?_⟩
  change SplitBlock22.pureMap a + (SplitBlock22.mixedMap g z + SplitBlock22.childMap h d) = -t
  have he' := congrArg (fun x => x + SplitBlock22.mixedMap g z) he
  rw [sub_add_cancel] at he'
  calc
    _ = SplitBlock22.pureMap a + SplitBlock22.childMap h d + SplitBlock22.mixedMap g z := by abel
    _ = _ := he'

/-- Actual corrected polynomial source columns, with prescribed mixed coefficients and their response. -/
theorem corrected_column (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) (a : Fin (4+(c+q)) → Forms K (3+m) 2)
    (ha : quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0)
    (t : SplitBlock22.Target K m)
    (ht : quadraticMultiplication (motionFamily p r s) a = SplitBlock22.targetEmbedding t)
    (z : Fin c → MiddleCoordinates.Mixed K m)
    (hz : MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z =
      -SplitBlock22.elimination (Submodule.span K (Set.range h)) t) :
    ∃ b : SplitBlock22.Source K m c q, b.2.1 = z ∧
      quadraticMultiplication (SplitBlock22.fullGenerators g h) (SplitBlock22.sourceEmbedding b) =
        -quadraticMultiplication (motionFamily p r s) a ∧
      (∀ ε : K, quadraticMultiplication (deformedFamily g h p r s ε)
        (a + ε • SplitBlock22.sourceEmbedding b) =
          ε^2 • quadraticMultiplication (motionFamily p r s) (SplitBlock22.sourceEmbedding b)) ∧
      projectionRawJ g h (quadraticMultiplication (motionFamily p r s) (SplitBlock22.sourceEmbedding b)) =
        (GeneralF13.combined g h).range.mkQ (∑ j, RowMultiplicationCoordinates.multiplication (p j) (z j)) := by
  obtain ⟨b,hb,hprod⟩ := prescribed_middle_completion g h t z hz
  have hc : quadraticMultiplication (SplitBlock22.fullGenerators g h) (SplitBlock22.sourceEmbedding b) =
      -quadraticMultiplication (motionFamily p r s) a := by
    rw [SplitBlock22.full_multiplication_commutes, hprod, ht]
    exact (SplitBlock22.targetEmbedding (K := K) (m := m)).map_neg t
  refine ⟨b,hb,hc,?_,?_⟩
  · intro ε
    rw [deformed_multiplication]
    exact deformation_second_response _ _ ε a _ ha hc
  · change (GeneralF13.combined g h).range.mkQ
      (projection13 (quadraticMultiplication (motionFamily p r s) (SplitBlock22.sourceEmbedding b))) = _
    rw [firstVariation_middle, hb]

/-- The pure first-response tensor reduces to the actual pure trace on homology. -/
theorem pureFirstResponse_elimination (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (a : (quadraticMultiplication (ThreeBlockModel.blockQuadrics (K := K))).ker) :
    SplitBlock22.elimination (Submodule.span K (Set.range h)) (pureFirstResponse r a.val) =
      AugmentedMiddle.pureTrace (fun i => (Submodule.span K (Set.range h)).mkQ (r i))
        (HomologyCoordinates.homologyClass a) := by
  rw [AugmentedMiddle.pureTrace_actual_coefficients]
  simp only [HomologyCoordinates.coefficientMap_mk,
    pureFirstResponse, map_sum, SplitBlock22.elimination_tmul]
  apply Prod.ext
  · exact Prod.fst_sum
  · exact Prod.snd_sum

/-- The concrete marked pure direction used in the simultaneous augmented open. -/
def markedDirection : Forms K 3 2 := ThreeBlockQuotient.square 0 - ThreeBlockQuotient.square 1

@[simp] theorem markedDirection_reduction :
    ThreeBlockQuotient.reduction (markedDirection (K := K)) = (1,-1) := by
  simp [markedDirection]

/-- The literal marked child response gives the anti-diagonal used by the correction space. -/
theorem marked_child_elimination (h : Fin q → Forms K m 2) (k : Fin q)
    (a : Fin q → Forms K m 2) :
    SplitBlock22.elimination (Submodule.span K (Set.range h))
      (childFirstResponse (Pi.single k markedDirection) a) =
        ((Submodule.span K (Set.range h)).mkQ (a k), -(Submodule.span K (Set.range h)).mkQ (a k)) := by
  classical
  have he : childFirstResponse (Pi.single k (markedDirection (K := K))) a =
      markedDirection ⊗ₜ[K] a k := by
    simp [childFirstResponse, Pi.single_apply, TensorProduct.ite_tmul]
  rw [he, SplitBlock22.elimination_tmul, markedDirection_reduction]
  simp


/-- Both orientations recover the identical mixed polynomial. -/
theorem traceRows_eq (a : Fin m → Forms K 3 1) :
    traceRows a = ActualTraceMotion.rowTraceEquiv.symm a := by
  obtain ⟨v,rfl⟩ := (ActualTraceMotion.rowTraceEquiv (K := K) (m := m)).surjective a
  rw [LinearEquiv.symm_apply_apply]
  change SplitBlock22.middleProjection
    (SplitBlock31.linearYEmbed (SplitBlock22.traceCoordinates v)) = v
  rw [SplitBlock22.linearYEmbed_traceCoordinates, SplitBlock22.middleProjection_mixedEmbedding]

/-- The literal order-one column has exactly the previously constructed trace response. -/
theorem trace_response_compatibility (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2)
    (a : LinearMap.ker (SplitMiddle31.multiplication (ActualTraceMotion.rowMixed g))) :
    projectionRawJ g h (quadraticMultiplication (motionFamily p r s)
      (SplitBlock31.sourceEmbedding a.val)) =
      ActualDeformationResponse.traceResponse g h r (Submodule.Quotient.mk a) := by
  change (GeneralF13.combined g h).range.mkQ
    (projection13 (quadraticMultiplication (motionFamily p r s) (SplitBlock31.sourceEmbedding a.val))) = _
  rw [firstVariation_trace,ActualDeformationResponse.traceResponse_mk]
  simp only [traceRows_eq]

/-- Every pure homology class has an actual polynomial cycle representative. -/
theorem pure_class_surjective : Function.Surjective (HomologyCoordinates.homologyClass (K := K)) := by
  exact Submodule.mkQ_surjective _

/-- An explicit representative condition for the marked old-child correction space. -/
def MarkedRepresentatives (h : Fin q → Forms K m 2) (k : Fin q)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) : Prop :=
  ∀ u : markedU, ∃ a : (quadraticMultiplication h).ker,
    (Submodule.span K (Set.range h)).mkQ (a.val k) = u.val

/-- An actual middle correction preimage has actual pure and marked-child source representatives. -/
theorem trace_preimage_representatives (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2) (k : Fin q)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k markedU)
    (z : (MovingMiddleCorrection.traceSpace h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    ∃ bx : (quadraticMultiplication (ThreeBlockModel.blockQuadrics (K := K))).ker,
    ∃ byCycle : (quadraticMultiplication h).ker,
      MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z.val =
        SplitBlock22.elimination (Submodule.span K (Set.range h))
          (pureFirstResponse r bx.val + childFirstResponse (Pi.single k markedDirection) byCycle.val) := by
  have hz := z.property
  change ∃ u, MovingMiddleCorrection.traceMap
    (fun i => (Submodule.span K (Set.range h)).mkQ (r i)) markedU u =
      MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z.val at hz
  obtain ⟨⟨u,ξ⟩,he⟩ := hz
  obtain ⟨bx,hbx⟩ := pure_class_surjective ξ
  obtain ⟨byCycle,hby⟩ := hmarked u
  refine ⟨bx,byCycle,?_⟩
  rw [map_add,pureFirstResponse_elimination,marked_child_elimination,hbx,hby,← he]
  apply Prod.ext <;> simp only [MovingMiddleCorrection.traceMap_apply,Prod.fst_add,Prod.snd_add] <;> abel


/-- The actual marked child coefficient on the actual child cycle space. -/
def childMarkedCoefficient (h : Fin q → Forms K m 2) (k : Fin q) :
    (quadraticMultiplication h).ker →ₗ[K] (Forms K m 2 ⧸ Submodule.span K (Set.range h)) :=
  (Submodule.span K (Set.range h)).mkQ.comp
    ((LinearMap.proj k).comp (quadraticMultiplication h).ker.subtype)

/-- The canonical marked space needs no representative assumption. -/
theorem canonical_marked_representatives (h : Fin q → Forms K m 2) (k : Fin q) :
    MarkedRepresentatives h k (childMarkedCoefficient h k).range := by
  intro u
  obtain ⟨a,ha⟩ := u.property
  exact ⟨a,ha⟩

/-- Every literal correction preimage is the second response of an actual corrected source
column. The only marked input is a representative condition on actual old-child cycles. -/
theorem correction_response_realized (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k markedU)
    (z : (MovingMiddleCorrection.traceSpace h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    ∃ a a₁ : Fin (4+(c+q)) → Forms K (3+m) 2,
      quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0 ∧
      quadraticMultiplication (SplitBlock22.fullGenerators g h) a₁ =
        -quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a ∧
      (∀ ε : K, quadraticMultiplication (deformedFamily g h p r (Pi.single k markedDirection) ε)
        (a + ε • a₁) = ε^2 • quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a₁) ∧
      projectionRawJ g h (quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a₁) =
        ActualDeformationResponse.correctionResponse g h r markedU p (Submodule.Quotient.mk z) := by
  classical
  obtain ⟨bx,byCycle,hz⟩ := trace_preimage_representatives g h r k markedU hmarked z
  let a : Fin (4+(c+q)) → Forms K (3+m) 2 :=
    -(SplitBlock40.sourceEmbedding bx.val + sourceEmbedding04 byCycle.val)
  let t : SplitBlock22.Target K m :=
    -(pureFirstResponse r bx.val + childFirstResponse (Pi.single k markedDirection) byCycle.val)
  have ha : quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0 := by
    dsimp [a]
    rw [map_neg,map_add]
    have hx : quadraticMultiplication (SplitBlock22.fullGenerators g h)
        (SplitBlock40.sourceEmbedding bx.val) = 0 := by
      change quadraticMultiplication (SplitBlock31.generators
        (fun j => SplitBlock22.traceCoordinates (g j)) h) (SplitBlock40.sourceEmbedding bx.val) = 0
      rw [SplitBlock40.multiplication_commutes,bx.property,map_zero]
    rw [hx,multiplication_sourceEmbedding04,byCycle.property,map_zero,add_zero,neg_zero]
  have ht : quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a =
      SplitBlock22.targetEmbedding t := by
    dsimp [a,t]
    rw [map_neg,map_add,firstVariation_pure,firstVariation_child]
    rw [← neg_one_smul K (pureFirstResponse r bx.val + childFirstResponse (Pi.single k markedDirection) byCycle.val),
      map_smul,map_add]
    exact (neg_one_smul K _).symm
  have hzt : MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)) z.val =
      -SplitBlock22.elimination (Submodule.span K (Set.range h)) t := by
    dsimp [t]
    rw [← neg_one_smul K (pureFirstResponse r bx.val + childFirstResponse (Pi.single k markedDirection) byCycle.val),
      map_smul,neg_one_smul,neg_neg]
    exact hz
  obtain ⟨b,hb,hcancel,hpoly,hresponse⟩ :=
    corrected_column g h p r (Pi.single k markedDirection) a ha t ht z.val hzt
  refine ⟨a,SplitBlock22.sourceEmbedding b,ha,hcancel,hpoly,?_⟩
  rw [hresponse,ActualDeformationResponse.correctionResponse_mk]

/-- The actual first-order column realizes every class of trace homology. -/
theorem trace_class_realized (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (s : Fin q → Forms K 3 2) (ξ : SplitMiddle31.Homology (ActualTraceMotion.rowMixed g)) :
    ∃ a : Fin (4+(c+q)) → Forms K (3+m) 2,
      quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0 ∧
      (∀ ε : K, quadraticMultiplication (deformedFamily g h p r s ε) a =
        ε • quadraticMultiplication (motionFamily p r s) a) ∧
      projectionRawJ g h (quadraticMultiplication (motionFamily p r s) a) =
        ActualDeformationResponse.traceResponse g h r ξ := by
  induction ξ using Submodule.Quotient.induction_on with | H b =>
  refine ⟨SplitBlock31.sourceEmbedding b.val,?_,?_,?_⟩
  · change quadraticMultiplication (SplitBlock31.generators (ActualTraceMotion.rowMixed g) h)
      (SplitBlock31.sourceEmbedding b.val) = 0
    rw [SplitBlock31.multiplication_commutes,b.property,map_zero]
  · intro ε
    exact trace_first_order g h p r s b.val b.property ε
  · exact trace_response_compatibility g h p r s b

/-- The actual second-order corrected column realizes every correction homology class. -/
theorem correction_class_realized (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (k : Fin q) (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (hmarked : MarkedRepresentatives h k markedU)
    (ξ : MovingMiddleCorrection.Correction g h r markedU) :
    ∃ a a₁ : Fin (4+(c+q)) → Forms K (3+m) 2,
      quadraticMultiplication (SplitBlock22.fullGenerators g h) a = 0 ∧
      quadraticMultiplication (SplitBlock22.fullGenerators g h) a₁ =
        -quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a ∧
      (∀ ε : K, quadraticMultiplication (deformedFamily g h p r (Pi.single k markedDirection) ε)
        (a + ε • a₁) = ε^2 • quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a₁) ∧
      projectionRawJ g h (quadraticMultiplication (motionFamily p r (Pi.single k markedDirection)) a₁) =
        ActualDeformationResponse.correctionResponse g h r markedU p ξ := by
  induction ξ using Submodule.Quotient.induction_on with | H z =>
  exact correction_response_realized g h p r k markedU hmarked z

end Quartic.ActualDeformationColumns


