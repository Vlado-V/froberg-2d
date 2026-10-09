module

public import Froberg.Prefix

@[expose] public section

/-! Multiplying a relation by one fixed nonzero monomial shows that prefix
injectivity in one coefficient degree implies every smaller degree. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] {n d e s r : ℕ}

theorem prefix_lower_injective (hn : 0 < n) (hse : s ≤ e)
    (Q : Fin r → Forms K n d) (hQ : Function.Injective (prefixMultiplication Q e)) :
    Function.Injective (prefixMultiplication Q s) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  let p : Poly K n := monomial (Finsupp.single (⟨0,hn⟩ : Fin n) (e-s)) 1
  have hp : p.IsHomogeneous (e-s) := isHomogeneous_monomial 1 (by rw [Finsupp.degree_single])
  have hp0 : p ≠ 0 := by simp [p]
  let b : Fin r → Forms K n e := fun i => ⟨p*(a i).val,by
    simpa only [Forms,mem_homogeneousSubmodule,Nat.sub_add_cancel hse] using hp.mul (a i).property⟩
  have hb : prefixMultiplication Q e b=0 := by
    apply Subtype.ext
    have hh := congrArg Subtype.val ha
    simp only [prefixMultiplication_val,Submodule.coe_zero] at hh ⊢
    change (∑ i,(Q i).val*(p*(a i).val))=0
    rw [show (∑ i,(Q i).val*(p*(a i).val))=p*(∑ i,(Q i).val*(a i).val) by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring]
    rw [hh,mul_zero]
  have hb0 : b=0 := hQ (hb.trans (map_zero _).symm)
  funext i
  apply Subtype.ext
  have hh := congrArg (fun x : Fin r → Forms K n e => (x i).val) hb0
  change p*(a i).val=0 at hh
  exact (mul_eq_zero.mp hh).resolve_left hp0

end Froberg
