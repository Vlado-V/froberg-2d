module

public import Quartic.MarkedEndpoints
public import Quartic.SharedMarkedFlag

@[expose] public section

/-! A common exact upper-child flag, retaining the lower square only when needed. -/
noncomputable section
namespace Quartic.MarkedEndpointFlag
open Module MvPolynomial UniformEndpoint SharedChildFlag EndpointHomology
variable {K ι : Type*} [Field K] [Infinite K] {n : ℕ}
set_option maxHeartbeats 1500000

theorem principal_open (hn : 1≤n) (q : ℕ) (hq : q=upperEndpoint n)
    (f : (ι → K) → (Fin q → Forms K n 2))
    (hf : IsPolynomialFamily f) (hfSurj : Function.Surjective f)
    (hchild : MarkedEndpoints K n) :
    ∃ D : MvPolynomial ι K,(∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → SharedChildFlag.Data (f a) := by
  classical
  cases q with
  | zero => have hpos := upper_positive hn; omega
  | succ r =>
    have hlo := before_upper_positive n r (by omega)
    have hhi : Counts.chi n (r+1)≤0 := by rw [hq]; exact upper_nonpositive n
    have hle := upper_le_quadratics n
    by_cases hz : Counts.chi n (r+1)=0
    · obtain ⟨D,hD,hgood⟩ := quartic_open f hf hfSurj (hchild.1 (r+1) (by omega))
      refine ⟨D,hD,?_⟩
      intro a ha
      obtain ⟨hi,hd⟩ := hgood a ha
      have hc : finrank K (QuarticQuotient K n
          (Submodule.span K (Set.range (fun i => (f a i).val))))=0 := by
        rw [hd]
        change (Counts.chi n (r+1)).toNat=0
        rw [hz]; rfl
      have hsum := quartic_quotient_add_rank (f a)
      rw [hc,zero_add] at hsum
      have hsurj : Function.Surjective (quadraticMultiplication (f a)) := by
        apply LinearMap.range_eq_top.mp
        apply Submodule.eq_top_of_finrank_eq
        simpa only [finrank_quartics] using hsum
      have he := quartic_euler_identity (f a) hi
      rw [hc,hz] at he
      have hh : finrank K (QuarticHomology (f a))=0 := by omega
      refine ⟨hi,hsurj,Fin.last r,?_⟩
      rw [markedCycles_range]
      have hb := LinearMap.finrank_range_le (MarkedCoefficient.markedCoefficientMap (f a))
      rw [hh] at hb
      have hrange : finrank K (MarkedCoefficient.markedCoefficientMap (f a)).range = 0 :=
        Nat.eq_zero_of_le_zero hb
      simp only [Counts.delta,hz,neg_zero,hrange,Int.natCast_zero]
    · have hlower : lowerEndpoint n=r := by
        unfold lowerEndpoint
        rw [←hq,if_neg hz]
        omega
      have hmarked := hchild.2 (by rw [hlower]; exact hlo)
      rw [hlower] at hmarked
      obtain ⟨q₀,_,hd₀,v,hv⟩ := hmarked.expected
      obtain ⟨D,hD,hgood⟩ := SharedMarkedFlag.principal_open f hf hfSurj
        (hchild.1 r (by omega)) (hchild.1 (r+1) (by omega)) hlo hhi q₀ hd₀ v hv
      exact ⟨D,hD,fun a ha => conditions_data (f a) (hgood a ha)⟩

end Quartic.MarkedEndpointFlag
