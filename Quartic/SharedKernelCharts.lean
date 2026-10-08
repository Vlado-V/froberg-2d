import Quartic.KernelPolynomialCharts

/-!
# One shared matrix family and several kernel vectors

All q kernel vectors use the same original family parameters and selected
minor. Only their free vector coordinates are independent. Thus the actual
rational charts have p+q(n-r) parameters, which is the shared-coefficient
count needed for conditioned incidence.
-/
noncomputable section
namespace Quartic.SharedKernelCharts
open Matrix MvPolynomial SubspaceCharts KernelPolynomialCharts
variable {K I : Type*} [Field K] {a n r q : ℕ}

abbrev Parameters (I : Type*) (v : Fin r ↪ Fin n) (q : ℕ) := I ⊕ (Fin q × Outside v)

def index (v : Fin r ↪ Fin n) (i : Fin q) :
    ChartParameters (I := I) v → Parameters I v q :=
  Sum.elim Sum.inl (fun k => Sum.inr (i,k))

def numerator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    (Fin q × Fin n) → MvPolynomial (Parameters I v q) K :=
  fun z => rename (index v z.1) (KernelPolynomialCharts.numerator A u v z.2)

def denominator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    MvPolynomial (Parameters I v q) K :=
  rename Sum.inl (A.submatrix u v).det

@[simp] theorem eval_denominator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n)
    (t : I → K) (y : Fin q × Outside v → K) :
    eval (Sum.elim t y) (denominator A u v) = (KernelCharts.minor (evaluated A t) u v).det := by
  rw [denominator, eval_rename]
  change eval t (A.submatrix u v).det = _
  rw [(eval t).map_det]
  congr 1

@[simp] theorem eval_numerator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n)
    (t : I → K) (y : Fin q × Outside v → K) (i : Fin q) (k : Fin n) :
    eval (Sum.elim t y) (numerator A u v (i,k)) =
      eval (Sum.elim t (fun j => y (i,j))) (KernelPolynomialCharts.numerator A u v k) := by
  rw [numerator, eval_rename]
  have hf : Sum.elim t y ∘ index v i = Sum.elim t (fun j => y (i,j)) := by
    funext z
    cases z <;> rfl
  rw [hf]

 theorem rationalMap_eq_reconstruct (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n)
    (t : I → K) (y : Fin q × Outside v → K)
    (hdet : (KernelCharts.minor (evaluated A t) u v).det ≠ 0) :
    RationalImageAvoidance.rationalMap (numerator A u v) (denominator A u v) (Sum.elim t y) =
      fun z : Fin q × Fin n => KernelCharts.reconstruct (evaluated A t) u v (fun j => y (z.1,j)) z.2 := by
  funext z
  rcases z with ⟨i,k⟩
  have he := congrFun (KernelPolynomialCharts.rationalMap_eq_reconstruct A u v t
    (fun j => y (i,j)) hdet) k
  simpa only [RationalImageAvoidance.rationalMap, eval_numerator, eval_denominator,
    KernelPolynomialCharts.eval_denominator] using he

/-- There is one shared set of matrix parameters and q independent free-vector sets. -/
theorem parameter_count [Fintype I] (v : Fin r ↪ Fin n) :
    Fintype.card (Parameters I v q) = Fintype.card I + q*(n-r) := by
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,card_outside]

/-- Every q-tuple of actual kernel vectors occurs in one shared rational chart. -/
theorem cover_kernel_tuple (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K)
    (hdet : (KernelCharts.minor (evaluated A t) u v).det ≠ 0)
    (x : Fin q → Fin n → K) (hx : ∀ i, evaluated A t *ᵥ x i = 0) :
    ∃ p : Parameters I v q → K, (∀ i, p (Sum.inl i) = t i) ∧
      eval p (denominator A u v) ≠ 0 ∧
      RationalImageAvoidance.rationalMap (numerator A u v) (denominator A u v) p =
        fun z : Fin q × Fin n => x z.1 z.2 := by
  refine ⟨Sum.elim t (fun z => x z.1 z.2.val),fun _ => rfl,?_,?_⟩
  · simpa only [eval_denominator] using hdet
  · rw [rationalMap_eq_reconstruct A u v t _ hdet]
    funext z
    exact congrFun (KernelCharts.reconstruct_kernel (evaluated A t) u v hdet (x z.1) (hx z.1)) z.2

end Quartic.SharedKernelCharts
