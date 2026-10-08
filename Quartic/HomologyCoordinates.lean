import Quartic.ThreeBlockQuotient

/-!
# The displayed cycles as a basis of actual pure-block Koszul homology

Coefficient reduction kills every actual incoming Koszul boundary. The three
explicit cycles therefore give three independent homology classes, and the
proved homology dimension makes them a basis. The resulting coefficient maps
land in the actual pure quadratic quotient.
-/
noncomputable section
namespace Quartic.HomologyCoordinates
open Module MvPolynomial ThreeBlock ThreeBlockModel ThreeBlockQuotient
set_option maxHeartbeats 200000
variable {K : Type*} [Field K]

abbrev Source (K : Type*) [Field K] := Fin 4 → Forms K 3 2
abbrev BlockHomology (K : Type*) [Field K] := QuarticHomology (blockQuadrics (K := K))

/-- The three displayed polynomial cycles as homogeneous quadratic arrays. -/
def cycles (j : Fin 3) (i : Fin 4) : Forms K 3 2 :=
  ⟨(![quarticCycle₁, quarticCycle₂, quarticCycle₃] j) i, by
    fin_cases j <;> fin_cases i <;> simp [quarticCycle₁, quarticCycle₂, quarticCycle₃, x, y, z]
    all_goals first | exact isHomogeneous_X_pow _ _ |
      exact ((isHomogeneous_X K _).mul (isHomogeneous_X K _)).neg |
      exact (isHomogeneous_X K _).mul (isHomogeneous_X K _)⟩

/-- Linear combinations of the actual displayed cycles. -/
def cycleCombination : (Fin 3 → K) →ₗ[K] Source K :=
  ∑ j : Fin 3, LinearMap.smulRight (LinearMap.proj j) (cycles j)

theorem cycleCombination_val (t : Fin 3 → K) (i : Fin 4) :
    (cycleCombination t i).val = quarticCombination t i := by
  simp [cycleCombination, cycles, Fin.sum_univ_succ, quarticCombination, smul_eq_C_mul, add_assoc]

@[simp] theorem cycleCombination_single (j : Fin 3) :
    cycleCombination (Pi.single j (1 : K)) = cycles j := by
  classical
  simp [cycleCombination, Pi.single_apply]

theorem multiplication_val (b : Source K) :
    (quadraticMultiplication blockQuadrics b).val = relation (fun i => (b i).val) := by
  simp [quadraticMultiplication, mulQuadratic, relation, Fin.sum_univ_succ]
  ring

theorem cycleCombination_is_cycle (t : Fin 3 → K) :
    quadraticMultiplication blockQuadrics (cycleCombination t) = 0 := by
  apply Subtype.ext
  rw [multiplication_val]
  change relation (fun i => (cycleCombination t i).val) = 0
  simpa only [cycleCombination_val] using quarticCombination_is_cycle t

theorem cycles_is_cycle (j : Fin 3) :
    quadraticMultiplication blockQuadrics (cycles (K := K) j) = 0 := by
  simpa only [cycleCombination_single] using cycleCombination_is_cycle (Pi.single j (1 : K))

private def kernelClass {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (B : Submodule K V) :
    f.ker →ₗ[K] KernelModulo f B := (kernelBoundary f B).mkQ

private def classOfCycleMap {V W A : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup A] [Module K A]
    (f : V →ₗ[K] W) (B : Submodule K V) (L : A →ₗ[K] V) (h : ∀ a, f (L a) = 0) :
    A →ₗ[K] KernelModulo f B :=
  (kernelClass f B).comp (L.codRestrict f.ker h)

/-- Passage from an actual cycle to its homology class. -/
def homologyClass : (quadraticMultiplication (blockQuadrics (K := K))).ker →ₗ[K] BlockHomology K :=
  kernelClass _ _

/-- The linear map taking coordinates to their actual homology classes. -/
def cycleClasses : (Fin 3 → K) →ₗ[K] BlockHomology K :=
  classOfCycleMap (quadraticMultiplication blockQuadrics) (koszulSpace blockQuadrics)
    cycleCombination cycleCombination_is_cycle

/-- Reduce all four actual quadratic coefficients. -/
def coefficientReduction : Source K →ₗ[K] (Fin 4 → K × K) :=
  LinearMap.pi (fun i => reduction.comp (LinearMap.proj i))

theorem coefficientReduction_koszul (p : GeneratorPair 4) :
    coefficientReduction (koszulVector (blockQuadrics (K := K)) p) = 0 := by
  funext i
  change reduction ((if i = p.val.1 then blockQuadrics p.val.2 else 0) -
    (if i = p.val.2 then blockQuadrics p.val.1 else 0)) = 0
  rw [map_sub]
  split_ifs <;> simp only [reduction_quadric, map_zero, sub_self]

theorem coefficientReduction_kills_boundaries :
    koszulSpace (blockQuadrics (K := K)) ≤ LinearMap.ker coefficientReduction := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact coefficientReduction_koszul p

private def descendKernel {V W A : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup A] [Module K A]
    (f : V →ₗ[K] W) (B : Submodule K V) (L : V →ₗ[K] A) (h : B ≤ L.ker) :
    KernelModulo f B →ₗ[K] A :=
  (kernelBoundary f B).liftQ (L.comp f.ker.subtype) (fun _ hx => h hx)

/-- Coefficient reduction on actual homology, well defined modulo boundaries. -/
def homologyReduction : BlockHomology K →ₗ[K] (Fin 4 → K × K) :=
  descendKernel (quadraticMultiplication blockQuadrics) (koszulSpace blockQuadrics)
    coefficientReduction coefficientReduction_kills_boundaries

theorem homologyReduction_cycleClasses (t : Fin 3 → K) (i : Fin 4) :
    homologyReduction (cycleClasses t) i =
      (coefficientMaps t i 0, coefficientMaps t i 1) := by
  change reduction (cycleCombination t i) = _
  rw [reduction_eq, cycleCombination_val, quarticCombination_reduction]

theorem cycleClasses_injective : Function.Injective (cycleClasses (K := K)) := by
  intro a b hab
  apply coefficientMaps_injective
  funext i j
  have h := congrFun (congrArg homologyReduction hab) i
  rw [homologyReduction_cycleClasses, homologyReduction_cycleClasses] at h
  fin_cases j
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Every actual homology class is a unique combination of the displayed cycles. -/
def homologyEquiv : (Fin 3 → K) ≃ₗ[K] BlockHomology K :=
  cycleClasses.linearEquivOfInjective cycleClasses_injective
    (by simp [BlockHomology, blockHomology_finrank])

/-- The displayed three quartic cycles form a basis of actual first homology. -/
def homologyBasis : Basis (Fin 3) K (BlockHomology K) :=
  (Pi.basisFun K (Fin 3)).map homologyEquiv

@[simp] theorem homologyBasis_apply (j : Fin 3) :
    homologyBasis (K := K) j = cycleClasses (Pi.single j 1) := by
  simp [homologyBasis, homologyEquiv, Pi.basisFun_apply]

/-- The basis vectors are precisely the classes of the three displayed arrays. -/
theorem homologyBasis_representative (j : Fin 3) :
    homologyBasis (K := K) j = homologyClass ⟨cycles j, cycles_is_cycle j⟩ := by
  rw [homologyBasis_apply]
  change homologyClass ⟨cycleCombination (Pi.single j 1), _⟩ = _
  congr 1
  apply Subtype.ext
  exact cycleCombination_single j

/-- The actual coefficient map `R_i : H_X → P`. -/
def coefficientMap (i : Fin 4) : BlockHomology K →ₗ[K] PureQuotient K :=
  quotientEquiv.symm.toLinearMap.comp ((LinearMap.proj i).comp homologyReduction)

/-- On cycle representatives this map is exactly extraction modulo the pure relations. -/
theorem coefficientMap_mk (i : Fin 4)
    (b : LinearMap.ker (quadraticMultiplication (blockQuadrics (K := K)))) :
    coefficientMap i (homologyClass b) =
      (pureSpace (K := K)).mkQ (b.val i) := by
  apply quotientEquiv.injective
  change quotientEquiv (quotientEquiv.symm (homologyReduction
    (homologyClass b) i)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (quotientEquiv_mk (b.val i)).symm

/-- The manuscript's displayed coefficient matrix is the matrix of actual `R_i`. -/
theorem coefficientMap_coordinates (t : Fin 3 → K) (i : Fin 4) :
    quotientEquiv (coefficientMap i (homologyEquiv t)) =
      (coefficientMaps t i 0, coefficientMaps t i 1) := by
  change quotientEquiv (quotientEquiv.symm (homologyReduction (cycleClasses t) i)) = _
  rw [LinearEquiv.apply_symm_apply, homologyReduction_cycleClasses]

/-- The marked functional on the genuine pure quadratic quotient. -/
def markedFunctional : PureQuotient K →ₗ[K] K :=
  ((LinearMap.fst K K K) + (LinearMap.snd K K K)).comp quotientEquiv.toLinearMap

/-- Apply the marked functional `ell(u,v)=u+v` to all actual coefficient maps. -/
def scalarCoefficientMap : BlockHomology K →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi (fun i => ((LinearMap.fst K K K) + (LinearMap.snd K K K)).comp
    ((LinearMap.proj i).comp homologyReduction))

theorem scalarCoefficientMap_is_marked (h : BlockHomology K) (i : Fin 4) :
    scalarCoefficientMap h i = markedFunctional (coefficientMap i h) := by
  simp [scalarCoefficientMap, markedFunctional, coefficientMap]

theorem scalarCoefficientMap_coordinates (t : Fin 3 → K) :
    scalarCoefficientMap (homologyEquiv t) = scalarCoefficients t := by
  funext i
  change (homologyReduction (cycleClasses t) i).1 +
    (homologyReduction (cycleClasses t) i).2 = _
  rw [homologyReduction_cycleClasses]
  rfl

/-- The manuscript's determinant `-2` proves injectivity on actual homology. -/
theorem scalarCoefficientMap_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (scalarCoefficientMap (K := K)) := by
  intro a b hab
  obtain ⟨s, rfl⟩ := homologyEquiv.surjective a
  obtain ⟨t, rfl⟩ := homologyEquiv.surjective b
  rw [scalarCoefficientMap_coordinates, scalarCoefficientMap_coordinates] at hab
  exact congrArg homologyEquiv (scalarCoefficients_injective h2 hab)

end Quartic.HomologyCoordinates
