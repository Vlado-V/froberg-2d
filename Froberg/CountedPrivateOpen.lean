import Froberg.CountSequences
import Froberg.PrivateGenericModel

/-! The private-column open with exactly the counts selected for the theorem. -/
noncomputable section
namespace Froberg
open Filter Module MvPolynomial VectorExpansionOpen
open scoped Topology

theorem exact_counts_private_strict_open {K : Type*} [Field K] [Infinite K]
    {d k h lo b : ℕ} (hd : 3 ≤ d) (hk : 0 < k) (hh : h=k*centralHalfBinomial d)
    (upper : Bool) (a f e : ℕ → ℕ) (ha : ∀ n,a n ≤ n)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∃ G : ℝ,0 < G ∧ ∀ᶠ n in atTop,
      ∃ D : MvPolynomial (VectorParameters.Index h n (d-1) (f n+b)) K,
        (∃ p,eval p D ≠ 0) ∧ ∀ p,eval p D ≠ 0 →
          StrictModel (VectorParameters.generators p) d (G*(n : ℝ)^d) := by
  obtain ⟨hat,hzt,har,hzr⟩ := exact_conditions_core_limits hd hk hh upper a f e ha hc
  have hd' : d-1+1=d := by omega
  have hh' : h=k*(2*(d-1)+1).choose (d-1) := by
    simpa only [centralHalfBinomial,show 2*(d-1)+1=2*d-1 by omega] using hh
  obtain ⟨G,hG,hopen⟩ := PrivateColumns.eventually_private_strict_open (K := K) (b := b)
    hk (by omega : 2 ≤ d-1) hh' a (fun n => n-a n) hat hzt
    (by simpa only [hd'] using har) (by simpa only [hd'] using hzr)
    (fun n => Nat.add_sub_of_le (ha n))
  refine ⟨G,hG,?_⟩
  filter_upwards [hopen,hc] with n hn hcn
  have hcard : Fintype.card (OuterInjection.Labels k (a n) (d-1) ⊕ Fin b)=f n+b := by
    rw [hcn.outer_eq]
    simp only [OuterInjection.Labels,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
      Sym.card_sym_eq_choose]
  rw [hcard,Nat.add_sub_of_le (ha n),hd'] at hn
  exact hn

end Froberg
