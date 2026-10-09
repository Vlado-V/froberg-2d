module

public import Froberg.CoefficientMotion
public import Quartic.SliceMotionAvoidance
public import Quartic.AuxiliaryMotionMatrix
public import Quartic.AuxiliarySurjectivity

@[expose] public section

/-! The C.6 passage from closed covector slices to maximal rank of the
actual coefficient motion. The matrix equations and the auxiliary columns
are constructed explicitly. -/
noncomputable section
namespace Froberg.CoefficientMotion
open Module Matrix MvPolynomial Quartic
open BilinearCovectorCharts BilinearCoefficientKernel KernelPolynomialCharts
open PolynomialBilinearCoordinates
variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
variable {a b T f e : ℕ}
variable (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
variable (E : H →ₗ[K] (Fin f → Fin a → K))

abbrev AugmentedInput (K : Type*) [Field K] (f b T e : ℕ) :=
  AuxiliaryMotionMatrix.Input K (Fintype.card (Fin f × Fin b)) T e

def augmentedPolynomialConstraint :
    Matrix (Fin (finrank K (AuxiliaryMotionMatrix.Output K (finrank K H) e)))
      (Fin (finrank K (AugmentedInput K f b T e))) (MvPolynomial (Fin T) K) :=
  AuxiliaryMotionMatrix.polynomialMatrix (e := e) (finitePolynomialConstraint mu E) X

@[simp] theorem augmentedPolynomialConstraint_rank (ell : Fin T → K) (hell : ell ≠ 0) :
    (evaluated (augmentedPolynomialConstraint (e := e) mu E) ell).rank =
      (constraint mu E ell).rank+e := by
  rw [augmentedPolynomialConstraint,AuxiliaryMotionMatrix.polynomialMatrix_rank]
  · simp only [evaluated_finitePolynomialConstraint,finiteConstraint_rank]
  · simpa only [eval_X] using hell

theorem augmentedPolynomialConstraint_scaling (c : K) (ell : Fin T → K) :
    evaluated (augmentedPolynomialConstraint (e := e) mu E) (c • ell) =
      c • evaluated (augmentedPolynomialConstraint (e := e) mu E) ell := by
  rw [augmentedPolynomialConstraint,AuxiliaryMotionMatrix.evaluated_polynomialMatrix,
    AuxiliaryMotionMatrix.evaluated_polynomialMatrix]
  simp only [eval_X,evaluated_finitePolynomialConstraint]
  have hs : finiteConstraint mu E (c • ell) = c • finiteConstraint mu E ell := by
    ext i j
    have ht := polynomialConstraint_scaling mu E c ell
    rw [evaluated_polynomialConstraint,evaluated_polynomialConstraint] at ht
    exact congrFun (congrFun ht i) ((Fintype.equivFin (Fin f × Fin b)).symm j)
  have he : AuxiliaryMotionMatrix.entries (finiteConstraint mu E (c • ell)) (c • ell) =
      c • AuxiliaryMotionMatrix.entries (finiteConstraint mu E ell) ell := by
    rw [hs]
    funext i
    cases i <;> rfl
  rw [he,map_smul,map_smul]

/-- The augmented matrix kernel is exactly the common annihilator of the
actual coefficient motion and the freely adjoined target columns. -/
theorem augmentedPolynomialConstraint_kernel_iff (ell : Fin T → K)
    (z : AugmentedInput K f b T e) :
    evaluated (augmentedPolynomialConstraint mu E) ell *ᵥ coordinates K _ z = 0 ↔
      (covector ell).comp (motion mu E (unflatten z.1)) = 0 ∧
      ∀ j, covector ell (z.2 j) = 0 := by
  rw [augmentedPolynomialConstraint,AuxiliaryMotionMatrix.polynomialMatrix_kernel_iff]
  simp only [eval_X,evaluated_finitePolynomialConstraint,finiteConstraint_kernel_iff]

/-- Closed projective strata with enough independent slice equations give
one common motion and auxiliary family excluding every nonzero covector.
The strata may be the determinantal kernel thresholds from C.4. -/
theorem exists_motion_excluding_covectors [Infinite K] [IsAlgClosed K]
    (hE : Function.Injective E)
    (count slices : Fin (a+1) → ℕ)
    (degrees : ∀ k, Fin (count k) → ℕ)
    (eqs : ∀ k, (i : Fin (count k)) → Forms K T (degrees k i))
    (cuts : ∀ k, Fin (slices k) → Forms K T 1)
    (hempty : ∀ k (ell : Fin T → K),
      (∀ i, aeval ell (eqs k i).val = 0) →
      (∀ j, aeval ell (cuts k j).val = 0) → ell = 0)
    (hcover : ∀ (ell : Fin T → K) (k : Fin (a+1)),
      finrank K (LinearMap.ker (relationMap mu ell)) = k.val →
      ∀ i, eval ell (eqs k i).val = 0)
    (hcount : ∀ k, slices k ≤ (finrank K H-f*k.val)+e) :
    ∃ z : AugmentedInput K f b T e,
      ∀ ell : Fin T → K,
        (covector ell).comp (motion mu E (unflatten z.1)) = 0 →
        (∀ j, covector ell (z.2 j) = 0) → ell = 0 := by
  classical
  let A := augmentedPolynomialConstraint (e := e) mu E
  let n := finrank K (AugmentedInput K f b T e)
  have hc (k : Fin (a+1)) :
      ∃ P : MvPolynomial (Fin n ⊕ Fin 0) K,
        (∃ z, eval z P ≠ 0) ∧ ∀ z, eval z P ≠ 0 →
        ∀ ell : Fin T → K, ell ≠ 0 → (∀ i, eval ell (eqs k i).val = 0) →
          finrank K H-f*k.val+e ≤ (evaluated A ell).rank →
          evaluated A ell *ᵥ (fun i => z (.inl i)) ≠ 0 := by
    obtain ⟨P,hP,hgood⟩ := SliceMotionAvoidance.principal_open_projective
      (L := K) (degrees k) (eqs k) (cuts k) (hempty k)
      A (0 : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin T ⊕ Fin n) K))
      (augmentedPolynomialConstraint_scaling mu E)
      (by intros; ext i; exact Fin.elim0 i) (r₁ := finrank K H-f*k.val+e) (r₂ := 0) (by simpa using hcount k)
    refine ⟨P,hP,?_⟩
    intro z hz ell hell heqs hr
    have hh := hgood z hz ell hell heqs hr (Nat.zero_le _)
    exact hh.elim id (fun hn => False.elim (hn (by ext i; exact Fin.elim0 i)))
  choose P hP hgood using hc
  have hne (k : Fin (a+1)) : P k ≠ 0 := by
    obtain ⟨z,hz⟩ := hP k
    intro hp
    exact hz (by rw [hp,map_zero])
  obtain ⟨x,hx⟩ := nonempty_principal_intersection P hne
  let z : AugmentedInput K f b T e := (coordinates K _).symm (fun i => x (.inl i))
  refine ⟨z,?_⟩
  intro ell hmotion haux
  by_contra hell
  have hk : finrank K (LinearMap.ker (relationMap mu ell)) ≤ a := by
    simpa using (LinearMap.ker (relationMap mu ell)).finrank_le
  let k : Fin (a+1) := ⟨finrank K (LinearMap.ker (relationMap mu ell)),by omega⟩
  have hr : finrank K H-f*k.val+e ≤ (evaluated A ell).rank := by
    rw [augmentedPolynomialConstraint_rank mu E ell hell]
    exact Nat.add_le_add_right (constraint_rank_bound mu E hE ell) e
  have hn := hgood k x (hx k) ell hell (hcover ell k rfl) hr
  apply hn
  have hz := (augmentedPolynomialConstraint_kernel_iff mu E ell z).mpr ⟨hmotion,haux⟩
  simpa only [z,LinearEquiv.apply_symm_apply] using hz

/-- With exactly target-minus-source auxiliary columns, the constructed
actual coefficient motion has maximal rank. -/
theorem exists_maximal_motion [Infinite K] [IsAlgClosed K]
    (hE : Function.Injective E)
    (count slices : Fin (a+1) → ℕ)
    (degrees : ∀ k, Fin (count k) → ℕ)
    (eqs : ∀ k, (i : Fin (count k)) → Forms K T (degrees k i))
    (cuts : ∀ k, Fin (slices k) → Forms K T 1)
    (hempty : ∀ k (ell : Fin T → K),
      (∀ i, aeval ell (eqs k i).val = 0) →
      (∀ j, aeval ell (cuts k j).val = 0) → ell = 0)
    (hcover : ∀ (ell : Fin T → K) (k : Fin (a+1)),
      finrank K (LinearMap.ker (relationMap mu ell)) = k.val →
      ∀ i, eval ell (eqs k i).val = 0)
    (hcount : ∀ k, slices k ≤ (finrank K H-f*k.val)+(T-finrank K H)) :
    ∃ z : Fin f → Fin b → K,
      finrank K (motion mu E z).range = min (finrank K H) T := by
  obtain ⟨z,hz⟩ := exists_motion_excluding_covectors (e := T-finrank K H)
    mu E hE count slices degrees eqs cuts hempty hcover hcount
  refine ⟨unflatten z.1,?_⟩
  have he : finrank K (Fin T → K)-finrank K H = T-finrank K H := by simp
  let Z : Fin (finrank K (Fin T → K)-finrank K H) → (Fin T → K) :=
    fun i => z.2 (Fin.cast he i)
  have hh := AuxiliarySurjectivity.maximal_rank_of_covector_exclusion
    (motion mu E (unflatten z.1)) Z ?_
  · simpa using hh
  intro ell hmotion haux
  let c : Fin T → K := fun k => ell (Pi.single k 1)
  have hc : covector c = ell := by
    apply LinearMap.ext
    intro v
    conv_rhs => rw [← (Pi.basisFun K (Fin T)).sum_equivFun v]
    simp [covector,c,Pi.basisFun_apply,Pi.basisFun_equivFun,smul_eq_mul,mul_comm]
  have hc0 : c = 0 := hz c (by rwa [hc]) (by
    intro j
    rw [hc]
    have hj : Fin.cast he (Fin.cast he.symm j) = j := Fin.ext rfl
    simpa only [Z,hj] using haux (Fin.cast he.symm j))
  rw [← hc,hc0]
  ext v
  simp [BilinearCovectorCharts.covector_apply]

end Froberg.CoefficientMotion
