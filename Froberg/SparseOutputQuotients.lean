module

public import Froberg.ProjectedSparseInjection
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

/-! Sparse polynomial columns in an actual output subspace remain injective
modulo each of finitely many fixed output relation spaces. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K V I : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I]

/-- An actual linear projection with exactly the prescribed kernel. -/
def relationProjection (R : Submodule K V) : V →ₗ[K] V :=
  (Classical.choose R.exists_isCompl).projection R
    (Classical.choose_spec R.exists_isCompl).symm

@[simp] theorem relationProjection_kernel (R : Submodule K V) :
    (relationProjection R).ker=R := by
  exact Submodule.ker_projection _

/-- Restricting a relation space to an output subspace can only reduce its dimension. -/
theorem restricted_relation_finrank (O R : Submodule K V) :
    finrank K (R.comap O.subtype)≤finrank K R := by
  have hh : (R.comap O.subtype).map O.subtype≤R := by
    rintro x ⟨v,hv,rfl⟩
    exact hv
  simpa only [Submodule.finrank_map_subtype_eq] using Submodule.finrank_mono hh

/-- The quotient output dimension loses at most the ambient relation dimension. -/
theorem relationProjection_restricted_rank (O R : Submodule K V) :
    finrank K O-finrank K R≤finrank K (relationProjection (R.comap O.subtype)).range := by
  have hd := (relationProjection (R.comap O.subtype)).finrank_range_add_finrank_ker
  rw [relationProjection_kernel] at hd
  have hle := restricted_relation_finrank O R
  omega

/-- One unrestricted sparse coefficient tuple works modulo all output relations.
The kernels are literal intersections with the specified ambient spaces. -/
theorem sparse_output_quotients_open {n s d m b : ℕ}
    (O : Submodule K V) (R : I → Submodule K V)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ j,(e j).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {j : Fin m // e j≤β}≤b*β.degree.choose s)
    (hcap : ∀ i,b*(s+d).choose s≤finrank K O-finrank K (R i)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → O))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 → ∀ i (c : ℕ),c≤d →
        Function.Injective (AttachedMultiplication.multiplication (d := c) e
          (fun j => coordinates K O (relationProjection ((R i).comap O.subtype)
            ((coordinates K (Fin m → O)).symm x j)))) := by
  let F (i : I) : O →ₗ[K] (Fin (finrank K O) → K) :=
    (coordinates K O).toLinearMap.comp (relationProjection ((R i).comap O.subtype))
  apply projected_sparse_injection_open_of_divisor_bound e he b hdiv F
  intro i
  have heq : finrank K (F i).range=
      finrank K (relationProjection ((R i).comap O.subtype)).range := by
    rw [show (F i).range=(relationProjection ((R i).comap O.subtype)).range.map
      (coordinates K O).toLinearMap by exact LinearMap.range_comp _ _]
    exact (coordinates K O).finrank_map_eq _
  rw [heq]
  exact (hcap i).trans (relationProjection_restricted_rank O (R i))

/-- The actual output coefficient at a scalar monomial in a sparse product sum. -/
def sparseOutputCoefficient {n m d : ℕ} (e : Fin m → Fin n →₀ ℕ)
    (v : Fin m → V) (p : Fin m → Forms K n d) (β : Fin n →₀ ℕ) : V :=
  ∑ i : {i // e i≤β},(p i.val).val.coeff (β-e i.val) • v i.val

/-- Projected sparse injectivity excludes every polynomial combination whose
output coefficients all lie in the specified output relation space. -/
theorem sparse_zero_of_relation_coefficients {n m d : ℕ}
    (O R : Submodule K V) (e : Fin m → Fin n →₀ ℕ) (v : Fin m → O)
    (hinj : Function.Injective (AttachedMultiplication.multiplication (d := d) e
      (fun j => coordinates K O (relationProjection (R.comap O.subtype) (v j)))))
    (p : Fin m → Forms K n d)
    (hp : ∀ β,(sparseOutputCoefficient e v p β).val∈R) : p=0 := by
  apply hinj
  rw [map_zero]
  funext j
  apply MvPolynomial.ext
  intro β
  rw [AttachedMultiplication.coefficient_formula]
  have hmem : sparseOutputCoefficient e v p β ∈ R.comap O.subtype := hp β
  have hz : relationProjection (R.comap O.subtype) (sparseOutputCoefficient e v p β)=0 := by
    exact (show R.comap O.subtype≤(relationProjection (R.comap O.subtype)).ker from
      (relationProjection_kernel _).ge) hmem
  have hh := congrFun (congrArg (coordinates K O) hz) j
  simpa only [sparseOutputCoefficient,map_sum,map_smul,map_zero,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Pi.zero_apply,MvPolynomial.coeff_zero,Finsupp.zero_apply] using hh

/-- The resulting common open is stated directly using the coefficients of
actual polynomial product sums, with no quotient-coordinate hypothesis. -/
theorem sparse_output_relations_open {n s d m b : ℕ}
    (O : Submodule K V) (R : I → Submodule K V)
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ j,(e j).degree=s)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {j : Fin m // e j≤β}≤b*β.degree.choose s)
    (hcap : ∀ i,b*(s+d).choose s≤finrank K O-finrank K (R i)) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → O))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 → ∀ i (c : ℕ),c≤d →
        ∀ p : Fin m → Forms K n c,
          (∀ β,(sparseOutputCoefficient e ((coordinates K (Fin m → O)).symm x) p β).val∈R i) →
          p=0 := by
  obtain ⟨D,hD,hgood⟩ := sparse_output_quotients_open O R e he hdiv hcap
  refine ⟨D,hD,?_⟩
  intro x hx i c hc p hp
  exact sparse_zero_of_relation_coefficients O (R i) e _ (hgood x hx i c hc) p hp

end Froberg
