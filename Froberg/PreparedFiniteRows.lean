module

public import Froberg.PreparedWitnessEmbedding
public import Froberg.FiniteEvenRow
public import Froberg.BiformKernelIntersection

@[expose] public section

/-! Finite capacity hypotheses produce actual row witnesses inside one common
prepared parameter space. No row-specific coefficient variables remain. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial AttachedMultiplication Quartic.PolynomialBilinearCoordinates
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

/-- Output constraints written as literal homogeneous kernels. -/
def constrainedOutputs {w : ℕ}
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) (j : ℕ) :=
  homogeneousSubmodule (Fin w × Bool) K j ⊓ (T j).ker

/-- The explicit finite bounds used by the generic higher even-row witness. -/
structure HigherRowCapacity (w v d q b : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) (R : J) : Prop where
  hw : 0<w
  hv : 0<v
  positive : ∀ j∈J,0<j
  even : ∀ j∈J,Even j
  degree : ∀ j∈J,j≤d
  new_unconstrained : T R.val=0
  diagonal : ∀ p : ProductRows.Row J R.val,p.val.val=R.val-p.val.val →
    counts p.val.val≤(w.choose p.val.val-finrank K X)*(v.choose (d-p.val.val)/2)
  cross : ∀ p : ProductRows.Row J R.val,p.val.val≠R.val-p.val.val →
    counts p.val.val≤((w+p.val.val-1).choose p.val.val-finrank K X)*(v+(d-p.val.val)-1).choose (d-p.val.val) ∧
    counts (R.val-p.val.val)≤((w+(R.val-p.val.val)-1).choose (R.val-p.val.val)-finrank K X)*
      (v+(d-(R.val-p.val.val))-1).choose (d-(R.val-p.val.val))
  output_positive : 0<oddOutputDimension w R.val
  enough_generators : counts R.val≤b*(v+v+(d-R.val)-1).choose (d-R.val)
  divisor_capacity : b*((d-R.val)+d).choose (d-R.val)≤oddOutputDimension w R.val
  incidence : oddOutputDimension w R.val*((d-R.val)+d).choose (d-R.val) *
    (Fintype.card (Label q J counts)+oddOutputDimension w R.val*(v+v+(d-R.val)-1).choose (d-R.val)+
      (oddOutputDimension w R.val*2^(oddOutputDimension w R.val))*(v+v+(d-1)-1).choose (d-1)) ≤
    (oddOutputDimension w R.val-b*((d-R.val)+d).choose (d-R.val))*(v+v+(d-R.val)+d-1).choose d
  scalar_open : ∃ D : MvPolynomial
      (Fin (finrank K (Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d))) K,
    (∃ Q : Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d,
      eval (coordinates K _ Q) D≠0) ∧
    ∀ Q : Fin (Fintype.card (Label q J counts)) → Forms K (v+v) d,
      eval (coordinates K _ Q) D≠0 →
      Function.Injective (ProjectedPrefix.multiplication
        (parityProfileRetained (balancedScalarHalf v) (d%2) (2*((d-R.val/2)/2))) Q (d-R.val))

/-- The complete finite construction lands in the prescribed common family. -/
theorem exists_higher_row_parameter {w v d q b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
    {T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X} (R : J)
    (h : HigherRowCapacity w v d q b J counts T R) :
    ∃ p : Space (v+v) d q J counts (constrainedOutputs T),
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
      (row (fun _ _ => inf_le_left) R p).ker=
        (rowConstants (fun _ _ => inf_le_left) R p).range := by
  obtain ⟨o,e,z,he,Q,E,ho,hdeg,hER,hRdeg,hrest,hzero,hker⟩ :=
    exists_finite_even_row h.hw h.hv counts J h.positive h.even h.degree T
      h.diagonal h.cross h.output_positive h.enough_generators h.divisor_capacity h.incidence h.scalar_open
  have hmem : ∀ j∈J,∀ i,E j i∈biformImage (constrainedOutputs T j) (Forms K (v+v) (d-j)) := by
    intro j hj i
    by_cases hjR : j=R.val
    · subst j
      rw [hER i,constrainedOutputs,h.new_unconstrained,LinearMap.ker_zero,inf_top_eq]
      rw [← polynomialFormVector_attachedCoordinates o e z he i]
      exact polynomialFormVector_mem_biform o _ _ hdeg _ (fun a => (attachedCoordinates e z he i a).property)
    · apply mem_biformImage_inf_kernel
      · apply mem_biformImage_of_homogeneous
        · simpa only [Nat.add_sub_of_le (h.degree j hj)] using (hrest j hjR i).1
        · exact (hrest j hjR i).2.1
      · exact (hrest j hjR i).2.2
  exact sparse_witness_common_parameter (fun _ _ => inf_le_left) R o ho hdeg e z he Q E hmem hER hzero hker

end Froberg.PreparedParameters
