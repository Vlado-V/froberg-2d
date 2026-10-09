module

public import Mathlib.Data.Nat.Basic

@[expose] public section

/-! Plain data for certificate lookup. Tree shape and lookup correctness are not
trusted: all uses separately check the resulting row and support equations. -/
namespace Quartic.FiniteEndpointLookup

/-- A finite lookup tree carrying absolute split indices. -/
inductive Table (α : Type*) where
  | leaf : α → Table α
  | node : ℕ → Table α → Table α → Table α

/-- Lookup traverses only the selected branch. Certificate queries are bounded
separately, so no completeness or ordering assumption on the tree is required. -/
def Table.get {α : Type*} : Table α → ℕ → α
  | .leaf x, _ => x
  | .node pivot left right, i =>
      if i < pivot then left.get i else right.get i

end Quartic.FiniteEndpointLookup
