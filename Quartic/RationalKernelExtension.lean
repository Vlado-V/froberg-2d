import Quartic.RationalMatrixPullback

/-!
# Successive kernel constraints along rational parameterizations

A kernel vector is appended to a rationally parameterized earlier choice.
The next matrix may depend polynomially on all earlier choices. Clearing
its denominators preserves its kernel and rank, and the new chart adds
exactly n-r free parameters. Iterating this construction therefore respects
successive dependence rather than assuming independent constraint groups.
-/
noncomputable section
namespace Quartic.RationalKernelExtension
open Matrix MvPolynomial RationalImageAvoidance KernelPolynomialCharts
variable {K I J : Type*} [Field K] {a n r : ℕ}

abbrev Parameters (I : Type*) (v : Fin r ↪ Fin n) := ChartParameters (I := I) v

def matrix (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K)) :=
  (RationalMatrixPullback.data F G A).matrix

def denominator (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) : MvPolynomial (Parameters I v) K :=
  rename Sum.inl G * KernelPolynomialCharts.denominator (matrix F G A) u v

def numerator (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) :
    J ⊕ Fin n → MvPolynomial (Parameters I v) K :=
  Sum.elim (fun j => rename Sum.inl (F j) * KernelPolynomialCharts.denominator (matrix F G A) u v)
    (fun k => KernelPolynomialCharts.numerator (matrix F G A) u v k * rename Sum.inl G)

 theorem eval_denominator (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : SubspaceCharts.Outside v → K) :
    eval (Sum.elim t y) (denominator F G A u v) =
      eval t G * (KernelCharts.minor (evaluated (matrix F G A) t) u v).det := by
  simp [denominator, eval_rename]

 theorem rationalMap_eq (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K) (y : SubspaceCharts.Outside v → K)
    (hG : eval t G ≠ 0)
    (hdet : (KernelCharts.minor (evaluated (matrix F G A) t) u v).det ≠ 0) :
    rationalMap (numerator F G A u v) (denominator F G A u v) (Sum.elim t y) =
      Sum.elim (rationalMap F G t) (KernelCharts.reconstruct (evaluated (matrix F G A) t) u v y) := by
  have hker := KernelPolynomialCharts.rationalMap_eq_reconstruct (matrix F G A) u v t y hdet
  funext j
  cases j with
  | inl j =>
    simp only [rationalMap,numerator,Sum.elim_inl,map_mul,eval_rename,
      Function.comp_def,eval_denominator,KernelPolynomialCharts.eval_denominator]
    field_simp
  | inr k =>
    have hk := congrFun hker k
    change eval (Sum.elim t y) (KernelPolynomialCharts.numerator (matrix F G A) u v k) /
      eval (Sum.elim t y) (KernelPolynomialCharts.denominator (matrix F G A) u v) = _ at hk
    rw [KernelPolynomialCharts.eval_denominator] at hk
    simp only [rationalMap,numerator,Sum.elim_inr,map_mul,eval_rename,
      Function.comp_def,eval_denominator]
    rw [← hk]
    field_simp
    rfl

/-- An actual next kernel vector is covered with no parameters beyond its
free coordinates; all earlier rationally reconstructed choices are retained. -/
theorem cover_at_minor (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K)
    (hG : eval t G ≠ 0)
    (hdet : (KernelCharts.minor (evaluated (matrix F G A) t) u v).det ≠ 0)
    (x : Fin n → K) (hx : evaluated A (rationalMap F G t) *ᵥ x = 0) :
    ∃ p : Parameters I v → K,
      (∀ i, p (Sum.inl i) = t i) ∧ eval p (denominator F G A u v) ≠ 0 ∧
      rationalMap (numerator F G A u v) (denominator F G A u v) p =
        Sum.elim (rationalMap F G t) x := by
  have hx' : evaluated (matrix F G A) t *ᵥ x = 0 :=
    ((RationalMatrixPullback.data F G A).mulVec_eq_zero_iff t hG x).mpr hx
  refine ⟨Sum.elim t (KernelCharts.outside v x), fun _ => rfl, ?_, ?_⟩
  · rw [eval_denominator]
    exact mul_ne_zero hG hdet
  · rw [rationalMap_eq F G A u v t _ hG hdet,
      KernelCharts.reconstruct_kernel _ u v hdet x hx']

/-- Rank at least r supplies one of finitely many charts for the dependent
kernel constraint. -/
theorem cover (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial J K)) (t : I → K)
    (hG : eval t G ≠ 0) (hr : r ≤ (evaluated A (rationalMap F G t)).rank)
    (x : Fin n → K) (hx : evaluated A (rationalMap F G t) *ᵥ x = 0) :
    ∃ u : Fin r ↪ Fin a, ∃ v : Fin r ↪ Fin n, ∃ p : Parameters I v → K,
      (∀ i, p (Sum.inl i) = t i) ∧ eval p (denominator F G A u v) ≠ 0 ∧
      rationalMap (numerator F G A u v) (denominator F G A u v) p =
        Sum.elim (rationalMap F G t) x := by
  have hr' : r ≤ (evaluated (matrix F G A) t).rank := by
    rw [matrix,(RationalMatrixPullback.data F G A).rank_eq t hG]
    exact hr
  obtain ⟨u,v,hdet⟩ := KernelCharts.exists_minor_of_rank_le _ hr'
  exact ⟨u,v,cover_at_minor F G A u v t hG hdet x hx⟩

 theorem parameter_count [Fintype I] (v : Fin r ↪ Fin n) :
    Fintype.card (Parameters I v) = Fintype.card I + (n-r) :=
  KernelPolynomialCharts.parameter_count v

end Quartic.RationalKernelExtension
