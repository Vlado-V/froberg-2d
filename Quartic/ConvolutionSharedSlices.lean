module

public import Quartic.ClosedCovectorMotionAvoidance
public import Quartic.MiddleCoordinates

@[expose] public section

/-!
# One shared child tuple for every closed convolution threshold

Each individual threshold open is pulled back by a surjective linear
projection from the same child tuple and all auxiliary slice tuples.
Their finite product is nonzero, so all closed thresholds can be excluded
simultaneously without assuming a common child tuple in advance.
-/
noncomputable section
namespace Quartic.ConvolutionSharedSlices
open Module MvPolynomial ProfileCertificate UniformEndpoint ConvolutionClosedSlices
open BilinearCoefficientKernel BilinearCovectorCharts ClosedCovectorEquations
variable {K : Type*} [Field K]

abbrev Threshold (m : ℕ) (upper : Bool) := Fin (totalA m (mixedCount m upper)+1)

/-- One actual child tuple, shared by every threshold, and one slice tuple
of the literal prescribed size for each threshold. -/
abbrev Input (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  (Fin (upperEndpoint m) → Fin (finrank K (Coeff K m upper)) → K) ×
    ((d : Threshold m upper) → Fin (sliceCount m upper d.val) →
      Fin (finrank K (Tgt K m upper)) → K)

/-- The threshold projection preserves the shared child tuple. -/
def projection (m : ℕ) (upper : Bool) (d : Threshold m upper) :
    Input K m upper →ₗ[K] SlicedInput K m upper d.val where
  toFun x := (x.1,x.2 d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem projection_apply (m : ℕ) (upper : Bool) (d : Threshold m upper)
    (x : Input K m upper) : projection m upper d x=(x.1,x.2 d) := rfl

theorem projection_surjective (m : ℕ) (upper : Bool) (d : Threshold m upper) :
    Function.Surjective (projection (K := K) m upper d) := by
  classical
  intro x
  refine ⟨(x.1,Function.update 0 d x.2),?_⟩
  simp only [projection_apply,Function.update_self]

/-- The same surjective map in the finite bases used by the individual
principal-open certificates. -/
def coordinateProjection (m : ℕ) (upper : Bool) (d : Threshold m upper) :
    (Fin (finrank K (Input K m upper)) → K) →ₗ[K]
      (Fin (finrank K (SlicedInput K m upper d.val)) → K) :=
  (PolynomialBilinearCoordinates.coordinates K _).toLinearMap.comp
    ((projection m upper d).comp
      (PolynomialBilinearCoordinates.coordinates K _).symm.toLinearMap)

@[simp] theorem coordinateProjection_coordinates (m : ℕ) (upper : Bool)
    (d : Threshold m upper) (x : Input K m upper) :
    coordinateProjection m upper d (PolynomialBilinearCoordinates.coordinates K _ x)=
      PolynomialBilinearCoordinates.coordinates K _ (projection m upper d x) := by
  simp only [coordinateProjection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- A nonempty principal open in one shared parameter space excludes every
closed relation-kernel threshold, including both endpoint thresholds. -/
theorem principal_open_all_thresholds [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    ∃ P : MvPolynomial (Fin (finrank K (Input K m upper))) K,
      (∃ x : Input K m upper,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : Input K m upper,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ d : Threshold m upper,∀ ell : Fin (finrank K (Tgt K m upper)) → K,
          d.val ≤ finrank K (LinearMap.ker (relationMap (actualMu m upper ht) ell)) →
          ((∀ i v,covector ell (actualMu m upper ht (x.1 i) v)=0) ∧
            (∀ j,covector ell (x.2 d j)=0)) → ell=0 := by
  classical
  choose P hP hgood using fun d : Threshold m upper =>
    principal_open_closed_sliced_empty (K := K) m hmlo hmhi upper ht d.val
  let pulled (d : Threshold m upper) :=
    MiddleCoordinates.substituteLinear (coordinateProjection (K := K) m upper d) (P d)
  have hpull (d : Threshold m upper) : pulled d ≠ 0 := by
    obtain ⟨x,hx⟩ := hP d
    obtain ⟨y,hy⟩ := projection_surjective m upper d x
    have hev : eval (PolynomialBilinearCoordinates.coordinates K _ y) (pulled d) ≠ 0 := by
      simpa only [pulled,MiddleCoordinates.eval_substituteLinear,
        coordinateProjection_coordinates,hy] using hx
    intro hzero
    exact hev (by rw [hzero,map_zero])
  let product := ∏ d,pulled d
  have hproduct : product ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun d _ => hpull d)
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero hproduct
  refine ⟨product,⟨(PolynomialBilinearCoordinates.coordinates K _).symm z,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hz
  · intro x hx d ell hker hann
    have hd : eval (PolynomialBilinearCoordinates.coordinates K _ x) (pulled d) ≠ 0 := by
      change eval _ (∏ d,pulled d) ≠ 0 at hx
      rw [map_prod] at hx
      exact (Finset.prod_ne_zero_iff.mp hx) d (Finset.mem_univ d)
    have hd' : eval (PolynomialBilinearCoordinates.coordinates K _
        (projection m upper d x)) (P d) ≠ 0 := by
      simpa only [pulled,MiddleCoordinates.eval_substituteLinear,
        coordinateProjection_coordinates] using hd
    exact hgood d (projection m upper d x) hd' ell hker hann

/-- An actual witness with the same child coefficients at every threshold. -/
theorem exists_all_thresholds [Infinite K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    ∃ x : Input K m upper,
      ∀ d : Threshold m upper,∀ ell : Fin (finrank K (Tgt K m upper)) → K,
        d.val ≤ finrank K (LinearMap.ker (relationMap (actualMu m upper ht) ell)) →
        ((∀ i v,covector ell (actualMu m upper ht (x.1 i) v)=0) ∧
          (∀ j,covector ell (x.2 d j)=0)) → ell=0 := by
  obtain ⟨P,⟨x,hx⟩,hgood⟩ := principal_open_all_thresholds (K := K) m hmlo hmhi upper ht
  exact ⟨x,hgood x hx⟩

/-- Over an algebraically closed field, the common open gives simultaneous
geometric empty sections of the unsliced minor-and-child loci. The slice
equations remain separate, as required by SliceMotionAvoidance. -/
theorem principal_open_all_empty_sections [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    ∃ P : MvPolynomial (Fin (finrank K (Input K m upper))) K,
      (∃ x : Input K m upper,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0) ∧
      ∀ x : Input K m upper,
        eval (PolynomialBilinearCoordinates.coordinates K _ x) P ≠ 0 →
        ∀ d : Threshold m upper,∀ ell : Fin (finrank K (Tgt K m upper)) → K,
          (∀ i,aeval ell (finiteEquations (d := d.val)
            (actualMu m upper ht) (x.1,Fin.elim0) i).val=0) →
          (∀ j,aeval ell (linearForm (x.2 d j)).val=0) → ell=0 := by
  obtain ⟨P,hP,hgood⟩ := principal_open_all_thresholds (K := K) m hmlo hmhi upper ht
  refine ⟨P,hP,?_⟩
  intro x hx d
  have hd : d.val ≤ ∑ i,blocks m upper i := by
    rw [blocks_sum]
    exact Nat.le_of_lt_succ d.isLt
  exact ClosedCovectorMotionAvoidance.split_empty_section
    (actualMu m upper ht) x.1 (x.2 d) hd (hgood x hx d)

/-- The fixed convolution witness needed before varying the presentation:
one child tuple, every prescribed slice count, and geometric emptiness for
all closed thresholds. -/
theorem exists_all_empty_sections [IsAlgClosed K] (m : ℕ) (hmlo : 28 ≤ m)
    (hmhi : m ≤ 40) (upper : Bool) (ht : 2 ≤ coreP (mixedCount m upper)+1) :
    ∃ x : Input K m upper,
      ∀ d : Threshold m upper,∀ ell : Fin (finrank K (Tgt K m upper)) → K,
        (∀ i,aeval ell (finiteEquations (d := d.val)
          (actualMu m upper ht) (x.1,Fin.elim0) i).val=0) →
        (∀ j,aeval ell (linearForm (x.2 d j)).val=0) → ell=0 := by
  obtain ⟨P,⟨x,hx⟩,hgood⟩ := principal_open_all_empty_sections (K := K) m hmlo hmhi upper ht
  exact ⟨x,hgood x hx⟩

end Quartic.ConvolutionSharedSlices
