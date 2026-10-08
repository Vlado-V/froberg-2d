import Quartic.KernelCharts
import Quartic.RationalImageAvoidance

/-!
# Rational charts for kernels of polynomial matrix families

Selected kernel coordinates are given by the actual adjugate-over-determinant
formula. Each chart uses the original matrix parameters and n-r free kernel
coordinates. This constructs the rational charts rather than assuming them.
-/
noncomputable section
namespace Quartic.KernelPolynomialCharts
open MvPolynomial Matrix SubspaceCharts
variable {K I : Type*} [Field K] {a n r : ℕ}

abbrev ChartParameters (v : Fin r ↪ Fin n) := I ⊕ Outside v

def evaluated (A : Matrix (Fin a) (Fin n) (MvPolynomial I K)) (t : I → K) :
    Matrix (Fin a) (Fin n) K := A.map (eval t)

/-- Extend the matrix polynomials by the free kernel-coordinate variables. -/
def extended (A : Matrix (Fin a) (Fin n) (MvPolynomial I K)) (v : Fin r ↪ Fin n) :
    Matrix (Fin a) (Fin n) (MvPolynomial (ChartParameters (I := I) v) K) :=
  A.map (rename Sum.inl)

def pivot (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ChartParameters (I := I) v) K) :=
  (extended A v).submatrix u v

def denominator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    MvPolynomial (ChartParameters (I := I) v) K := (pivot A u v).det

def freeContribution (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    Fin r → MvPolynomial (ChartParameters (I := I) v) K :=
  fun i => ∑ j : Outside v, extended A v (u i) j.val * X (Sum.inr j)

def numerator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    Fin n → MvPolynomial (ChartParameters (I := I) v) K :=
  fun k => if h : k ∈ Set.range v then
    -((pivot A u v).adjugate *ᵥ freeContribution A u v)
      ((Equiv.ofInjective v v.injective).symm ⟨k, h⟩)
    else denominator A u v * X (Sum.inr ⟨k, h⟩)

@[simp] theorem eval_extended (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (v : Fin r ↪ Fin n) (t : I → K) (y : Outside v → K) (i : Fin a) (j : Fin n) :
    eval (Sum.elim t y) (extended A v i j) = evaluated A t i j := by
  simp [extended, evaluated, eval_rename]

@[simp] theorem eval_pivot (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : Outside v → K) :
    (pivot A u v).map (eval (Sum.elim t y)) = KernelCharts.minor (evaluated A t) u v := by
  ext i j
  exact eval_extended A v t y (u i) (v j)

@[simp] theorem eval_denominator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : Outside v → K) :
    eval (Sum.elim t y) (denominator A u v) = (KernelCharts.minor (evaluated A t) u v).det := by
  rw [denominator, (eval (Sum.elim t y)).map_det, RingHom.mapMatrix_apply, eval_pivot]

@[simp] theorem eval_freeContribution (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : Outside v → K) (i : Fin r) :
    eval (Sum.elim t y) (freeContribution A u v i) = KernelCharts.offPivot (evaluated A t) u v y i := by
  simp [freeContribution, KernelCharts.offPivot]

@[simp] theorem eval_adjugate_product (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : Outside v → K) (i : Fin r) :
    eval (Sum.elim t y) (((pivot A u v).adjugate *ᵥ freeContribution A u v) i) =
      ((KernelCharts.minor (evaluated A t) u v).adjugate *ᵥ
        KernelCharts.offPivot (evaluated A t) u v y) i := by
  rw [RingHom.map_mulVec]
  have ha := (eval (Sum.elim t y)).map_adjugate (pivot A u v)
  simp only [RingHom.mapMatrix_apply, eval_pivot] at ha
  rw [ha]
  congr 1
  funext j
  exact eval_freeContribution A u v t y j

/-- The polynomial numerators and denominator evaluate to the actual kernel reconstruction. -/
theorem rationalMap_eq_reconstruct (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : Outside v → K)
    (hdet : (KernelCharts.minor (evaluated A t) u v).det ≠ 0) :
    RationalImageAvoidance.rationalMap (numerator A u v) (denominator A u v) (Sum.elim t y) =
      KernelCharts.reconstruct (evaluated A t) u v y := by
  classical
  funext k
  by_cases hk : k ∈ Set.range v
  · simp only [RationalImageAvoidance.rationalMap, numerator, dite_eq_left hk, map_neg,
      eval_adjugate_product, eval_denominator, KernelCharts.reconstruct]
  · simp only [RationalImageAvoidance.rationalMap, numerator, dite_eq_right hk, map_mul,
      eval_denominator, eval_X, Sum.elim_inr, KernelCharts.reconstruct]
    exact mul_div_cancel_left₀ _ hdet

/-- Every actual kernel vector lies in a rational chart with the chosen nonsingular minor. -/
theorem kernel_in_chart (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K)
    (hdet : (KernelCharts.minor (evaluated A t) u v).det ≠ 0)
    (x : Fin n → K) (hx : evaluated A t *ᵥ x = 0) :
    ∃ p : ChartParameters (I := I) v → K,
      eval p (denominator A u v) ≠ 0 ∧
      RationalImageAvoidance.rationalMap (numerator A u v) (denominator A u v) p = x := by
  refine ⟨Sum.elim t (KernelCharts.outside v x), ?_, ?_⟩
  · simpa only [eval_denominator] using hdet
  · rw [rationalMap_eq_reconstruct A u v t _ hdet]
    exact KernelCharts.reconstruct_kernel _ u v hdet x hx

/-- Number of parameters in each chart, including the original matrix family. -/
theorem parameter_count [Fintype I] (v : Fin r ↪ Fin n) :
    Fintype.card (ChartParameters (I := I) v) = Fintype.card I + (n - r) := by
  rw [Fintype.card_sum, SubspaceCharts.card_outside]

end Quartic.KernelPolynomialCharts
