module

public import Froberg.TensorWeightTransport
public import Froberg.GradedProductAssembly

@[expose] public section

/-! A common four-block variable model for the cross and diagonal witnesses
in a fixed product row. -/
noncomputable section
namespace Froberg.FourBlocks
open MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {A B : Type*}

abbrev Variables (A B : Type*) := (A × Bool) ⊕ (B × Bool)

def leftVar : A ⊕ B → Variables A B
  | .inl x => .inl (x,true)
  | .inr y => .inr (y,true)

def rightVar : A ⊕ B → Variables A B
  | .inl x => .inl (x,false)
  | .inr y => .inr (y,false)

/-- Regrouping the two sides as paired output and paired scalar variables. -/
def regroup : ((A ⊕ B) ⊕ (A ⊕ B)) ≃ Variables A B where
  toFun := Sum.elim leftVar rightVar
  invFun := fun z => match z with
    | .inl (x,b) => if b then .inl (.inl x) else .inr (.inl x)
    | .inr (y,b) => if b then .inl (.inr y) else .inr (.inr y)
  left_inv := by rintro ((x|y)|(x|y)) <;> rfl
  right_inv := by
    rintro (⟨x,b⟩|⟨y,b⟩) <;> cases b <;> rfl

def xHalfWeight : Variables A B → ℕ
  | .inl (x,b) => if b then 1 else 0
  | .inr _ => 0

def yHalfWeight : Variables A B → ℕ
  | .inl _ => 0
  | .inr (y,b) => if b then 1 else 0

def outputWeight : A ⊕ B → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)
def scalarWeight : A ⊕ B → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- One cross-pair witness has independent products in the same variable
model used for all diagonal-pair witnesses. -/
theorem cross_products_independent {α β : Type*} [Fintype α] [Fintype β]
    (a : α → MvPolynomial (A ⊕ B) K) (b : β → MvPolynomial (A ⊕ B) K)
    (ha : LinearIndependent K a) (hb : LinearIndependent K b) :
    LinearIndependent K (fun p : α × β => rename leftVar (a p.1) * rename rightVar (b p.2)) := by
  have h := (linearIndependent_cross_products_disjoint a b ha hb).map'
    (rename (regroup (A := A) (B := B))).toLinearMap
    (LinearMap.ker_eq_bot.mpr (rename_injective _ regroup.injective))
  convert h using 1
  funext p
  simp only [Function.comp_apply,AlgHom.toLinearMap_apply,map_mul,rename_rename]
  rfl

theorem leftVar_weighted_output {a : MvPolynomial (A ⊕ B) K} {j : ℕ}
    (ha : a.IsWeightedHomogeneous outputWeight j) :
    (rename leftVar a).IsWeightedHomogeneous xHalfWeight j := by
  apply rename_weightedHomogeneous
    (⟨leftVar,regroup.injective.comp Sum.inl_injective⟩ : (A ⊕ B) ↪ Variables A B)
    outputWeight xHalfWeight _ ha
  rintro (x|y) <;> rfl

theorem rightVar_weighted_output (a : MvPolynomial (A ⊕ B) K) :
    (rename rightVar a).IsWeightedHomogeneous xHalfWeight 0 := by
  apply rename_weightedHomogeneous
    (⟨rightVar,regroup.injective.comp Sum.inr_injective⟩ : (A ⊕ B) ↪ Variables A B)
    (fun _ => 0) xHalfWeight _ (weightedHomogeneous_zero_weight a)
  rintro (x|y) <;> rfl

theorem leftVar_weighted_scalar {a : MvPolynomial (A ⊕ B) K} {j : ℕ}
    (ha : a.IsWeightedHomogeneous scalarWeight j) :
    (rename leftVar a).IsWeightedHomogeneous yHalfWeight j := by
  apply rename_weightedHomogeneous
    (⟨leftVar,regroup.injective.comp Sum.inl_injective⟩ : (A ⊕ B) ↪ Variables A B)
    scalarWeight yHalfWeight _ ha
  rintro (x|y) <;> rfl

theorem rightVar_weighted_scalar (a : MvPolynomial (A ⊕ B) K) :
    (rename rightVar a).IsWeightedHomogeneous yHalfWeight 0 := by
  apply rename_weightedHomogeneous
    (⟨rightVar,regroup.injective.comp Sum.inr_injective⟩ : (A ⊕ B) ↪ Variables A B)
    (fun _ => 0) yHalfWeight _ (weightedHomogeneous_zero_weight a)
  rintro (x|y) <;> rfl

end Froberg.FourBlocks
