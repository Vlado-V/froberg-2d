import Quartic.PolynomialSubspaceCovectorCharts
import Quartic.ProjectiveKernelIncidence

/-!
# Projective tuple charts over arbitrary polynomial subspace charts

The original chart parameters are retained, and one nonzero tuple coefficient
is normalized to one. For d displayed spanning vectors the exact count is
g+qd-1. Coverage is proved for every nonzero tuple in the actual vector span;
linear independence is not assumed implicitly.
-/

noncomputable section
namespace Quartic.PolynomialSubspaceTupleCharts
open Module Matrix MvPolynomial KernelPolynomialCharts
open PolynomialSubspaceCovectorCharts (vector subspace)
variable {K I : Type*} [Field K] {a q d n b : ℕ}

abbrev Pivot (q d : ℕ) := Fin q × Fin d
abbrev ParameterIndex (I : Type*) (z : Pivot q d) := I ⊕ {p : Pivot q d // p ≠ z}

theorem parameter_count [Fintype I] (z : Pivot q d) :
    Fintype.card (ParameterIndex I z)=Fintype.card I+q*d-1 := by
  classical
  have hpos : 0 < q*d := Nat.mul_pos (Fin.pos z.1) (Fin.pos z.2)
  have ho : Fintype.card {p : Pivot q d // p ≠ z}=q*d-1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Pivot,Fintype.card_prod,Fintype.card_fin,Fintype.card_subtype_eq]
  rw [Fintype.card_sum,ho]
  omega

def selectedPolynomial (z : Pivot q d) (i : Fin q) (h : Fin d) :
    MvPolynomial (ParameterIndex I z) K :=
  if he : (i,h)=z then 1 else X (Sum.inr ⟨(i,h),he⟩)

def tuplePolynomial (H : Fin d → Fin a → MvPolynomial I K)
    (z : Pivot q d) (i : Fin q) (k : Fin a) : MvPolynomial (ParameterIndex I z) K :=
  ∑ h : Fin d,selectedPolynomial z i h * rename Sum.inl (H h k)

def tupleMap (H : Fin d → Fin a → MvPolynomial I K)
    (z : Pivot q d) (p : ParameterIndex I z → K) : Fin q → Fin a → K :=
  fun i k => eval p (tuplePolynomial H z i k)

theorem tupleMap_eq_sum (H : Fin d → Fin a → MvPolynomial I K)
    (z : Pivot q d) (p : ParameterIndex I z → K) (i : Fin q) :
    tupleMap H z p i=
      ∑ h : Fin d,eval p (selectedPolynomial z i h) • vector H (fun j => p (.inl j)) h := by
  funext k
  simp [tupleMap,tuplePolynomial,vector,eval_rename,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Function.comp_def]

def encode (z : Pivot q d) (t : I → K) (U : Fin q → Fin d → K) : ParameterIndex I z → K :=
  Sum.elim t (fun h => U h.val.1 h.val.2)

theorem selectedPolynomial_encode (z : Pivot q d) (t : I → K) (U : Fin q → Fin d → K)
    (hU : U z.1 z.2=1) (i : Fin q) (h : Fin d) :
    eval (encode z t U) (selectedPolynomial z i h)=U i h := by
  classical
  by_cases he:(i,h)=z
  · have hi : i=z.1 := congrArg Prod.fst he
    have hh : h=z.2 := congrArg Prod.snd he
    simp [selectedPolynomial,hi,hh,hU]
  · simp [selectedPolynomial,he,encode]

theorem tupleMap_encode (H : Fin d → Fin a → MvPolynomial I K)
    (z : Pivot q d) (t : I → K) (U : Fin q → Fin d → K) (hU : U z.1 z.2=1) (i : Fin q) :
    tupleMap H z (encode z t U) i=∑ h : Fin d,U i h • vector H t h := by
  rw [tupleMap_eq_sum]
  have ht : (fun j => encode z t U (.inl j))=t := rfl
  rw [ht]
  apply Finset.sum_congr rfl
  intro h _
  rw [selectedPolynomial_encode z t U hU]

/-- Every nonzero tuple inside an actual polynomial span is covered, retaining
the original parameters and introducing just qd-1 normalized coefficients. -/
theorem cover_tuple (H : Fin d → Fin a → MvPolynomial I K) (t : I → K)
    (F : Fin q → Fin a → K) (hF : F ≠ 0) (hmem : ∀ i,F i ∈ subspace H t) :
    ∃ z : Pivot q d,∃ p : ParameterIndex I z → K,∃ s : K,
      s ≠ 0 ∧ (∀ j,p (.inl j)=t j) ∧ F=s • tupleMap H z p := by
  classical
  choose U hU using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hmem i)
  obtain ⟨i₀,h₀,hnz⟩ : ∃ i h,U i h ≠ 0 := by
    by_contra! hz
    apply hF
    funext i
    rw [← hU i]
    simp [hz]
  let z : Pivot q d := (i₀,h₀)
  let s : K := U i₀ h₀
  have hs : s ≠ 0 := hnz
  let U' : Fin q → Fin d → K := fun i h => s⁻¹*U i h
  have hU' : U' z.1 z.2=1 := inv_mul_cancel₀ hnz
  refine ⟨z,encode z t U',s,hnz,fun _ => rfl,?_⟩
  funext i
  change F i=s • tupleMap H z (encode z t U') i
  rw [tupleMap_encode H z t U' hU',Finset.smul_sum]
  simpa only [U',smul_smul,← mul_assoc,mul_inv_cancel₀ hs,one_mul] using (hU i).symm

/-- The actual relation equation matrix on a normalized polynomial tuple chart. -/
def equationMatrix (B : (Fin q → Fin a → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    (H : Fin d → Fin a → MvPolynomial I K) (z : Pivot q d) :
    Matrix (Fin b) (Fin n) (MvPolynomial (ParameterIndex I z) K) :=
  fun j k => ∑ i : Fin q,∑ h : Fin a,
    tuplePolynomial H z i h * C (B (Pi.single i (Pi.single h 1)) (Pi.single k 1) j)

theorem eval_equationMatrix (B : (Fin q → Fin a → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    (H : Fin d → Fin a → MvPolynomial I K) (z : Pivot q d) (p : ParameterIndex I z → K) :
    evaluated (equationMatrix B H z) p=LinearMap.toMatrix' (B (tupleMap H z p)) := by
  classical
  ext j k
  change eval p (equationMatrix B H z j k)=_
  rw [LinearMap.toMatrix'_apply]
  conv_rhs => rw [ProjectiveKernelIncidence.tuple_expansion (tupleMap H z p)]
  simp [equationMatrix,tupleMap,map_sum,map_smul,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem equationMatrix_mulVec
    (B : (Fin q → Fin a → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    (H : Fin d → Fin a → MvPolynomial I K) (z : Pivot q d)
    (p : ParameterIndex I z → K) (x : Fin n → K) :
    evaluated (equationMatrix B H z) p *ᵥ x=B (tupleMap H z p) x := by
  rw [eval_equationMatrix,LinearMap.toMatrix'_mulVec]

theorem equationMatrix_rank
    (B : (Fin q → Fin a → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    (H : Fin d → Fin a → MvPolynomial I K) (z : Pivot q d) (p : ParameterIndex I z → K) :
    (evaluated (equationMatrix B H z) p).rank=finrank K (LinearMap.range (B (tupleMap H z p))) := by
  have he : (evaluated (equationMatrix B H z) p).mulVecLin=B (tupleMap H z p) :=
    LinearMap.ext (equationMatrix_mulVec B H z p)
  rw [Matrix.rank,he]

end Quartic.PolynomialSubspaceTupleCharts
