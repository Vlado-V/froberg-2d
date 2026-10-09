module

public import Froberg.DivisibilityCoupling
public import Quartic.HomogeneousCoefficientCoordinates

@[expose] public section

/-! The weighted incidence identities on the homogeneous-coordinate index type. -/
noncomputable section
namespace Froberg.MonomialExpansion
open Quartic.HomogeneousCoefficientCoordinates

def degreeSubtypeEquiv (n d : ℕ) : Exponent n d ≃ Degree n d where
  toFun a := ⟨a.val,mem_exponents.mpr a.property⟩
  invFun a := ⟨a.val,degree_val a⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma source_weight_sum_exponent {n d : ℕ} (b : Exponent n d) (e : ℕ) :
    ∑ a : Exponent n e, weight b.val a.val = d.choose e := by
  calc
    _ = ∑ a : Degree n e, weight b.val a.val := (degreeSubtypeEquiv n e).sum_comp _
    _ = _ := source_weight_sum (degreeSubtypeEquiv n d b) e

lemma target_weight_sum_exponent {n e d : ℕ} (hn : 0 < n) (a : Exponent n e) :
    ∑ b : Exponent n (e+d), weight b.val a.val = (n+e+d-1).choose d := by
  calc
    _ = ∑ b : Degree n (e+d), weight b.val a.val := (degreeSubtypeEquiv n (e+d)).sum_comp _
    _ = _ := by simpa [degreeSubtypeEquiv,Nat.add_assoc] using
      target_weight_sum hn (Nat.le_add_right e d) (degreeSubtypeEquiv n e a)

end Froberg.MonomialExpansion
