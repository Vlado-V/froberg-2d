module

public import Quartic.ActualDeformationColumns
public import Quartic.PolynomialRankOpen

@[expose] public section

/-! Independence of the actual split and perturbed quadratic families. -/
noncomputable section
namespace Quartic.DeformationIndependence
open Module MvPolynomial SplitBlock22 ActualDeformationColumns
variable {K : Type*} [Field K] {m c q : ℕ}
set_option maxHeartbeats 1000000

theorem split_independent (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    LinearIndependent K (fullGenerators g h) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hp := congrArg (SplitBlock31.coreProjection (K := K) (m := m)) ha
  have hm := congrArg (middleProjection (K := K) (m := m)) ha
  have hc := congrArg (childProjection (K := K) (m := m)) ha
  rw [map_sum,Fin.sum_univ_add,Fin.sum_univ_add] at hp hm hc
  simp only [map_smul,fullGenerators_pure,fullGenerators_mixed,fullGenerators_child,
    SplitBlock31.coreProjection_coreEmbed,coreProjection_mixedEmbedding,
    SplitBlock31.coreProjection_childEmbed,smul_zero,Finset.sum_const_zero,
    add_zero,map_zero] at hp
  simp only [map_smul,fullGenerators_pure,fullGenerators_mixed,fullGenerators_child,
    middleProjection_coreEmbed,middleProjection_mixedEmbedding,middleProjection_childEmbed,
    smul_zero,Finset.sum_const_zero,zero_add,add_zero,map_zero] at hm
  simp only [map_smul,fullGenerators_pure,fullGenerators_mixed,fullGenerators_child,
    childProjection_coreEmbed,childProjection_mixedEmbedding,childProjection_childEmbed,
    smul_zero,Finset.sum_const_zero,zero_add,map_zero] at hc
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact Fintype.linearIndependent_iff.mp ThreeBlockModel.blockQuadrics_independent _ hp j
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      exact Fintype.linearIndependent_iff.mp hg _ hm k
    · intro k
      exact Fintype.linearIndependent_iff.mp hh _ hc k

/-- The actual deformed quadrics stay independent on a determinant open
containing ε=0, which can be intersected with the rank-gain determinant. -/
theorem principal_open (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (p : Fin c → Forms K m 2) (r : Fin 4 → Forms K m 2) (s : Fin q → Forms K 3 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h) :
    ∃ D : MvPolynomial (Fin 1) K,eval (0 : Fin 1 → K) D≠0 ∧
      ∀ ε : K,eval (fun _ => ε) D≠0 → LinearIndependent K (deformedFamily g h p r s ε) := by
  have hpoly (i : Fin (4+(c+q))) : IsPolynomialFamily
      (fun a : Fin 1 → K => deformedFamily g h p r s (a 0) i) := by
    exact (isPolynomialFamily_const (fullGenerators g h i)).add
      ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul
        (isPolynomialFamily_const (motionFamily p r s i)))
  obtain ⟨D,hD,hgood⟩ := independent_polynomial_principal_open
    (fun i (a : Fin 1 → K) => deformedFamily g h p r s (a 0) i) hpoly 0
    (by simpa only [Pi.zero_apply,deformedFamily,zero_smul,add_zero] using split_independent g h hg hh)
  exact ⟨D,hD,fun ε hε => hgood (fun _ => ε) hε⟩

end Quartic.DeformationIndependence
