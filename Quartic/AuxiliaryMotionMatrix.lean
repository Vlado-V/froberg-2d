import Quartic.SharedCovectorPolynomial

/-! Adjoin freely chosen target columns to the second actual motion stage. -/
noncomputable section
namespace Quartic.AuxiliaryMotionMatrix
open Module Matrix MvPolynomial BilinearCovectorCharts KernelPolynomialCharts
open PolynomialBilinearCoordinates
variable {K I : Type*} [Field K] {a n T e : ℕ}

abbrev Input (K : Type*) [Field K] (n T e : ℕ) := (Fin n → K) × (Fin e → Fin T → K)
abbrev Output (K : Type*) [Field K] (a e : ℕ) := (Fin a → K) × (Fin e → K)
abbrev EntryIndex (a n T : ℕ) := (Fin a × Fin n) ⊕ Fin T

def entries (B : Matrix (Fin a) (Fin n) K) (ell : Fin T → K) : EntryIndex a n T → K :=
  Sum.elim (fun ij => B ij.1 ij.2) ell

def augmented (B : Matrix (Fin a) (Fin n) K) (ell : Fin T → K) :
    Input K n T e →ₗ[K] Output K a e :=
  B.mulVecLin.prodMap (CoefficientConstraintRank.repeated (covector ell))

def family : (EntryIndex a n T → K) →ₗ[K] Input K n T e →ₗ[K] Output K a e where
  toFun p := augmented (fun i j => p (.inl (i,j))) (fun k => p (.inr k))
  map_add' p q := by
    apply LinearMap.ext
    rintro ⟨y,Z⟩
    apply Prod.ext
    · funext i
      change (∑ j,(p (.inl (i,j))+q (.inl (i,j)))*y j) =
        (∑ j,p (.inl (i,j))*y j)+(∑ j,q (.inl (i,j))*y j)
      simp only [add_mul,Finset.sum_add_distrib]
    · funext j
      simp [augmented,CoefficientConstraintRank.repeated,covector_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c p := by
    apply LinearMap.ext
    rintro ⟨y,Z⟩
    apply Prod.ext
    · funext i
      change (∑ j,(c*p (.inl (i,j)))*y j)=c*(∑ j,p (.inl (i,j))*y j)
      simp only [Finset.mul_sum,mul_assoc]
    · funext j
      simp [augmented,CoefficientConstraintRank.repeated,covector_apply,Finset.mul_sum,mul_assoc]

@[simp] theorem family_entries (B : Matrix (Fin a) (Fin n) K) (ell : Fin T → K) :
    family (e := e) (entries B ell)=augmented (e := e) B ell := rfl

/-- Literal polynomial entries of the augmented motion map in fixed finite coordinates. -/
def polynomialMatrix (B : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (ell : Fin T → MvPolynomial I K) :
    Matrix (Fin (finrank K (Output K a e))) (Fin (finrank K (Input K n T e))) (MvPolynomial I K) :=
  fun i j => ∑ k : EntryIndex a n T,entries B ell k * C
    ((coordinate (family (K := K) (a := a) (n := n) (T := T) (e := e))
      (Pi.single k 1)) (Pi.single j 1) i)

/-- The augmented matrix is the actual product of the old constraint and
one scalar evaluation for each independent auxiliary target vector. -/
theorem evaluated_polynomialMatrix (B : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (ell : Fin T → MvPolynomial I K) (p : I → K) :
    evaluated (polynomialMatrix (e := e) B ell) p =
      LinearMap.toMatrix' (coordinate (family (e := e))
        (entries (evaluated B p) (fun k => eval p (ell k)))) := by
  classical
  ext i j
  change eval p (∑ k : EntryIndex a n T,entries B ell k * C
    ((coordinate family (Pi.single k 1)) (Pi.single j 1) i)) = _
  rw [map_sum]
  conv_rhs => rw [← (Pi.basisFun K (EntryIndex a n T)).sum_equivFun
    (entries (evaluated B p) (fun k => eval p (ell k)))]
  simp only [map_mul,eval_C,map_sum,map_smul,LinearMap.toMatrix'_apply,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,Pi.basisFun_apply,Pi.basisFun_equivFun,
    LinearEquiv.refl_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  cases k <;> rfl

/-- Every nonzero covector receives exactly e additional independent equations. -/
theorem rank_augmented (B : Matrix (Fin a) (Fin n) K) (ell : Fin T → K) (hell : ell ≠ 0) :
    finrank K (LinearMap.range (augmented (e := e) B ell)) = B.rank+e := by
  rw [augmented,LinearMap.range_prodMap,(Submodule.prodEquiv _ _).finrank_eq,Module.finrank_prod,
    CoefficientConstraintRank.finrank_range,
    Module.Dual.range_eq_top_of_ne_zero (SharedCovectorConstraints.covector_ne_zero ell hell),
    finrank_top,Module.finrank_self,Nat.mul_one]
  rfl

theorem polynomialMatrix_rank (B : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (ell : Fin T → MvPolynomial I K) (p : I → K)
    (hell : (fun k => eval p (ell k)) ≠ 0) :
    (evaluated (polynomialMatrix (e := e) B ell) p).rank = (evaluated B p).rank+e := by
  rw [evaluated_polynomialMatrix,Matrix.rank]
  have he (L : (Fin (finrank K (Input K n T e)) → K) →ₗ[K]
      (Fin (finrank K (Output K a e)) → K)) : (LinearMap.toMatrix' L).mulVecLin=L := by
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec L x
  rw [he,finrank_range_coordinate,family_entries]
  exact rank_augmented _ _ hell

/-- The polynomial kernel means that the old motion equation vanishes and
the same covector kills each freely chosen auxiliary target vector. -/
theorem polynomialMatrix_kernel_iff (B : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (ell : Fin T → MvPolynomial I K) (p : I → K) (y : Input K n T e) :
    evaluated (polynomialMatrix (e := e) B ell) p *ᵥ coordinates K _ y=0 ↔
      evaluated B p *ᵥ y.1=0 ∧ ∀ j,covector (fun k => eval p (ell k)) (y.2 j)=0 := by
  rw [evaluated_polynomialMatrix,LinearMap.toMatrix'_mulVec,coordinate_apply,
    LinearEquiv.symm_apply_apply,family_entries,LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h,fun j => congrFun (congrArg Prod.snd h) j⟩
  · rintro ⟨hB,hZ⟩
    exact Prod.ext hB (funext hZ)

/-- Homogeneous λ-scaling survives the auxiliary augmentation, with all
previous-stage motions held fixed. -/
theorem polynomialMatrix_scaling {n₁ : ℕ}
    (B : Matrix (Fin a) (Fin n) (MvPolynomial (Fin T ⊕ Fin n₁) K))
    (hB : ∀ (s : K) ell x,evaluated B (Sum.elim (s • ell) x)=s • evaluated B (Sum.elim ell x))
    (s : K) (ell : Fin T → K) (x : Fin n₁ → K) :
    evaluated (polynomialMatrix (e := e) B (fun k => X (Sum.inl k))) (Sum.elim (s • ell) x)=
      s • evaluated (polynomialMatrix (e := e) B (fun k => X (Sum.inl k))) (Sum.elim ell x) := by
  rw [evaluated_polynomialMatrix,evaluated_polynomialMatrix]
  simp only [eval_X,Sum.elim_inl]
  have he : entries (evaluated B (Sum.elim (s • ell) x)) (s • ell)=
      s • entries (evaluated B (Sum.elim ell x)) ell := by
    rw [hB]
    funext i
    cases i <;> rfl
  rw [he,map_smul,map_smul]

end Quartic.AuxiliaryMotionMatrix
