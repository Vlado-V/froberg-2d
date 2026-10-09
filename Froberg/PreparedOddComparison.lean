module

public import Froberg.PreparedExtraColumn
public import Froberg.PreparedBackgroundIndependent
public import Froberg.PreparedPrivateCertificate
public import Froberg.PreparedOuterSeparation
public import Froberg.PreparedThinProperty
public import Froberg.BackgroundChildDeletion
public import Froberg.ConcreteBackgroundComparison

@[expose] public section

/-! A finite prepared odd-degree point supplies the concrete critical
comparison. The extra column belongs to the enlarged point, while the
endpoint and thin-slice certificates belong to its retained restriction. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters BilinearScalarFamily VectorExpansionOpen
variable {K : Type} [Field K] [Infinite K]
variable {h m d q f u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

variable [IsAlgClosed K]

theorem exists_critical_comparison_of_prepared_odd
    {r : ℕ} {c c' : ℕ → ℕ}
    (hd : 1 < d) (ho : d%2=1) (hm : 0 < m) (upper : Bool)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hmin : ∀ j∈J,2≤j) (hJlt : ∀ j∈J,0<c' j → j<d)
    (hc : ∀ j∈J,c j≤c' j) (extra : ProductRows.LayerLabel J c')
    (hmiss : ∀ i,countLayerMap hc i≠extra)
    (hcover : ∀ j,(∃ i,countLayerMap hc i=j) ∨ j=extra)
    (hcard : upperCount m d+Fintype.card (ProductRows.LayerLabel J c)+f+u=
      adjacentCriticalCount upper (h+m) d)
    (idx : Fin r ≃ PreparedParameters.Label (upperCount m d) J c')
    (U : Fin u → Forms K h d)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d (upperCount m d) f u J c' O)
    (hp : ∀ j,LinearIndependent K (p.2.1.2 j)) (hP : LinearIndependent K p.1)
    (hiFull : LinearIndependent K (zeroScalarEndpointFamily (by omega) hO hJ U p.1 p.2))
    (hoddFull : OddCyclesExact U p.1 p.2)
    (hreduce : FullPreparedParameters.PrivateSplitReduction (by omega) ho hO hJ heven idx U p)
    (hsep : PreparedOuterSeparation (by omega) ho hO hJ heven U p)
    (hiBase : LinearIndependent K (zeroScalarEndpointFamily (by omega) hO hJ U p.1
      (restrictCounts hc p.2.1,p.2.2)))
    (hoddBase : OddCyclesExact U p.1 (restrictCounts hc p.2.1,p.2.2))
    (hupperBase : Function.Surjective (upperTargetMap (zeroScalarEndpointFamily (by omega) hO hJ U p.1
      (restrictCounts hc p.2.1,p.2.2))))
    (C : ℝ) (hC : (f : ℝ)≤C)
    (hthin : PreparedEndpointThin (by omega) ho hO hJ heven U C (fullRestrictCounts hc p))
    (G : ℝ)
    (hchild : ChildFlagCondition (quotientMultiplication (fun i => outerVectorEquiv.symm (p.2.2 i)) d)
      (outerScalarDeficit (fun i => outerVectorEquiv.symm (p.2.2 i))) G
      (coefficientCoordinates (fun i => p.2.1.1 (Sum.inl i)))) :
    Nonempty (LocalComparisonData K (h+m) d
      (adjacentCriticalCount upper (h+m) d) (criticalDefect K m d)) := by
  classical
  let hd0 : 0<d := by omega
  let Q : Fin (upperCount m d) → Forms K m d := fun i => p.2.1.1 (Sum.inl i)
  let E := preparedPositiveBiform hO hJ heven (restrictCounts hc p.2.1)
  let F := fun i => preparedOddBiform hd0 ho U p.1 p.2.2 (Sum.inl i)
  let P := fun i => preparedOddBiform hd0 ho U p.1 p.2.2 (Sum.inr i)
  let M := preparedEvenBiform hO hJ heven p.2.1 (Sum.inr extra)
  have hbase : preparedBaseBiform hO hJ heven (restrictCounts hc p.2.1)=
      (fun i => scalarEvenBiform (h := h) (Q i)) := by
    funext i
    rw [preparedBaseBiform_eq_scalar]
    rfl
  obtain ⟨hQ,hcok,hgeneric⟩ := childFlag_scalar_properties _ _ G Q hchild
  have hup := prepared_background_upper hd0 ho hO hJ heven U p.1
    (restrictCounts hc p.2.1,p.2.2) hupperBase
  rw [hbase] at hup
  obtain ⟨D,hdeleted,hD,hinj,hcoverage⟩ := exists_background_child_deletion Q E F P hcok hup
  have hpositive := prepared_extra_positive_independent hd0 ho hO hJ heven hc p.2.1 U p.1 p.2.2
    extra hmiss (prepared_positive_background_scalar_independent hd ho hO hmin hJ hJlt heven
      U p.1 p.2 hp hP)
  have hspan := prepared_extra_background_span hd0 ho hO hJ heven hc p.2.1 U p.1 p.2.2 extra hcover
  have hbackground := prepared_private_flag_formal_relations hd0 ho hO hJ heven
    (fun j hj => lt_of_lt_of_le (by omega : 0<2) (hmin j hj)) idx U p hiFull hoddFull hreduce D hD
  rw [hspan,←sup_assoc] at hbackground
  have hseparation := hsep D hD
  rw [hspan,←sup_assoc] at hseparation
  have hi := prepared_background_independent hd0 ho hO hJ heven U p.1
    (restrictCounts hc p.2.1,p.2.2) hiBase
  rw [hbase] at hi
  have hex := prepared_odd_split_exact hd0 ho hO hJ heven U p.1
    (restrictCounts hc p.2.1,p.2.2) hoddBase
  rw [hbase] at hex
  unfold PreparedEndpointThin at hthin
  change HasClosedKernelSlices
    (oddEndpointScalarAction
      (Fin.append (preparedBaseBiform hO hJ heven (restrictCounts hc p.2.1)) E) F P)
    (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension
      (Fin.append (preparedBaseBiform hO hJ heven (restrictCounts hc p.2.1)) E) F P) C) at hthin
  rw [hbase] at hthin
  exact exists_critical_comparison_of_concrete_background hm upper hcard D hD Q hQ E F P M
    hpositive hbackground hseparation hi hex hup hcoverage C hC hthin hgeneric hinj hdeleted

end Froberg.PreparedTarget
