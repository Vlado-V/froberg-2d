module

public import Froberg.QuadraticChildFlag
public import Quartic.MarkedDefect
public import Quartic.ActualDeformationColumns

@[expose] public section

/-! The actual marked child space, with both generic child defects retained. -/
noncomputable section
namespace Froberg.QuadraticMarkedFlag
open Module MvPolynomial Quartic UniformEndpoint ActualDeformationColumns
open FixedBlockChildOpen
variable {K : Type*} [Field K] [Infinite K] {n : ℕ}
set_option maxHeartbeats 1500000

def Data (q : Fin (upperEndpoint n) → Forms K n 2) : Prop :=
  LinearIndependent K q ∧
  finrank K (QuadraticChildFlag.Coker q)=genericCokernel K n 2 (upperEndpoint n) ∧
  ∃ k : Fin (upperEndpoint n),
    (finrank K (childMarkedCoefficient q k).range : ℤ)=
      Counts.delta n (upperEndpoint n)+genericCokernel K n 2 (upperEndpoint n)-
        genericHomology K n 2 (upperEndpoint n-1)

theorem principal_open (hn : 0<n) (h2 : (2 : K)≠0) :
    ∃ D : MvPolynomial (ChildIndex n (upperEndpoint n)) K,
      (∃ a,eval a D≠0) ∧ ∀ a,eval a D≠0 → Data (decode a) := by
  classical
  have hpos := SharedChildFlag.upper_positive (by omega : 1≤n)
  unfold Data
  generalize heq : upperEndpoint n=q at *
  cases q with
  | zero => omega
  | succ r =>
    have hr : r+1≤(n+1).choose 2 := by
      simpa only [heq] using upper_le_quadratics n
    have hchi : 0<Counts.chi n r := before_upper_positive n r (by omega)
    obtain ⟨D,hD,hgood⟩ := QuadraticChildFlag.principal_open (K := K) hn hr hchi h2
    refine ⟨D,hD,?_⟩
    intro a ha
    obtain ⟨hi,hc,hh,hsq⟩ := hgood a ha
    change LinearIndependent K (decode a) ∧ _
    refine ⟨hi,hc,Fin.last r,?_⟩
    have hmarked := MarkedDefect.marked_rank_add_old (decode a) hi hsq
    have heuler := quartic_euler_identity (decode a) hi
    have hrange : (childMarkedCoefficient (decode a) (Fin.last r)).range=
        (MarkedCoefficient.markedCoefficientMap (decode a)).range :=
      SharedChildFlag.markedCycles_range (decode a)
    rw [hrange]
    change (finrank K (QuadraticChildFlag.Coker (decode a)):ℤ)-_= _ at heuler
    rw [hc] at heuler
    rw [hh] at hmarked
    simp only [Counts.delta, Nat.add_sub_cancel]
    have hmarked' :
        (finrank K (MarkedCoefficient.markedCoefficientMap (decode a)).range : ℤ)+
          genericHomology K n 2 r = finrank K (QuarticHomology (decode a)) := by
      exact_mod_cast hmarked
    linear_combination hmarked' - heuler

end Froberg.QuadraticMarkedFlag
