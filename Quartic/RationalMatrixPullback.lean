module

public import Quartic.RationalComposition
public import Quartic.KernelPolynomialCharts

@[expose] public section

/-!
# Matrix families pulled back through rational charts

Substituting a rational chart in a polynomial matrix and clearing one common
denominator gives a genuine polynomial matrix family of exactly the same
rank and kernel on the original chart domain. This supplies the algebra for
successive, dependent kernel constraints in the deformation incidence.
-/
noncomputable section
namespace Quartic.RationalMatrixPullback
open Matrix MvPolynomial RationalImageAvoidance KernelPolynomialCharts
variable {K I J : Type*} [Field K] {a n : ℕ}

/-- Actual numerator matrix and common denominator power for a rational substitution. -/
structure Data (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (B : Matrix (Fin a) (Fin n) (MvPolynomial J K)) where
  matrix : Matrix (Fin a) (Fin n) (MvPolynomial I K)
  power : ℕ
  eval_matrix : ∀ p : I → K, eval p G ≠ 0 →
    evaluated matrix p = (eval p G)^power • evaluated B (rationalMap F G p)

/-- A finite matrix has one common denominator without any new parameters. -/
theorem exists_data (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (B : Matrix (Fin a) (Fin n) (MvPolynomial J K)) : Nonempty (Data F G B) := by
  classical
  obtain ⟨N,d,hN⟩ := RationalComposition.family_numerators F G
    (fun z : Fin a × Fin n => B z.1 z.2)
  refine ⟨⟨fun i j => N (i,j),d,?_⟩⟩
  intro p hp
  ext i j
  change eval p (N (i,j)) = (eval p G)^d * eval (rationalMap F G p) (B i j)
  rw [hN p hp (i,j)]
  field_simp

/-- Chosen polynomial data; all uses retain the proved evaluation identity. -/
def data (F : J → MvPolynomial I K) (G : MvPolynomial I K)
    (B : Matrix (Fin a) (Fin n) (MvPolynomial J K)) : Data F G B :=
  Classical.choice (exists_data F G B)

/-- Multiplying every matrix entry by a nonzero scalar preserves the actual kernel. -/
theorem ker_smul (B : Matrix (Fin a) (Fin n) K) (s : K) (hs : s ≠ 0) :
    LinearMap.ker (s • B).mulVecLin = LinearMap.ker B.mulVecLin := by
  ext x
  change (s • B) *ᵥ x = 0 ↔ B *ᵥ x = 0
  rw [Matrix.smul_mulVec]
  simp only [smul_eq_zero,hs,false_or]

/-- Every substituted matrix has exactly its cleared numerator rank on the chart domain. -/
theorem Data.rank_eq {F : J → MvPolynomial I K} {G : MvPolynomial I K}
    {B : Matrix (Fin a) (Fin n) (MvPolynomial J K)} (D : Data F G B)
    (p : I → K) (hp : eval p G ≠ 0) :
    (evaluated D.matrix p).rank = (evaluated B (rationalMap F G p)).rank := by
  rw [D.eval_matrix p hp]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp))

/-- Clearing the denominator also preserves all actual kernel vectors. -/
theorem Data.ker_eq {F : J → MvPolynomial I K} {G : MvPolynomial I K}
    {B : Matrix (Fin a) (Fin n) (MvPolynomial J K)} (D : Data F G B)
    (p : I → K) (hp : eval p G ≠ 0) :
    LinearMap.ker (evaluated D.matrix p).mulVecLin =
      LinearMap.ker (evaluated B (rationalMap F G p)).mulVecLin := by
  rw [D.eval_matrix p hp]
  exact ker_smul _ _ (pow_ne_zero _ hp)

 theorem Data.mulVec_eq_zero_iff {F : J → MvPolynomial I K} {G : MvPolynomial I K}
    {B : Matrix (Fin a) (Fin n) (MvPolynomial J K)} (D : Data F G B)
    (p : I → K) (hp : eval p G ≠ 0) (x : Fin n → K) :
    evaluated D.matrix p *ᵥ x = 0 ↔ evaluated B (rationalMap F G p) *ᵥ x = 0 := by
  change x ∈ LinearMap.ker (evaluated D.matrix p).mulVecLin ↔
    x ∈ LinearMap.ker (evaluated B (rationalMap F G p)).mulVecLin
  rw [D.ker_eq p hp]

end Quartic.RationalMatrixPullback
