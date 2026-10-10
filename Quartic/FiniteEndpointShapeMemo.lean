module

public import Quartic.FiniteEndpointCheckerLoad

@[expose] public section

/-! Reuse kernel-checked generator supports and product lookups in row proofs.
All computed certificate data remains untrusted until checked. -/
namespace Quartic.FiniteEndpointShapeMemo

/-- Keep the mapped function head identical in the generic map, each checked
lookup, and the reconstructed list. The definition is ordinary and transparent. -/
def mappedProduct {d : Nat} (product : Nat → Nat → Nat) (b j : Fin d) : Nat :=
  product j.val b.val

/-- Substituting a checked selector and support avoids reducing the support
filter in each row. The products themselves still have to be checked. -/
theorem rowShapeOfMemo {g d : Nat}
    (select : Nat → Fin g × Fin d) (support : Fin g → List (Fin d))
    (product : Nat → Nat → Nat) (i : Nat) (a : Fin g) (b : Fin d)
    (xs : List (Fin d)) (ys : List Nat)
    (hselect : select i = (a, b)) (hsupport : support a = xs)
    (hproducts : xs.map (mappedProduct product b) = ys) :
    (support (select i).1).map (fun j => product j.val (select i).2.val) = ys := by
  rw [hselect, hsupport]
  exact hproducts

open Lean Meta Elab Command
meta section

/-- Only closed syntax is cached. Kernel checking of every declaration still
checks its Fin constructor and proof; this cache contains no theorem results. -/
initialize finLiteralCache : IO.Ref (Std.HashMap (Nat × Nat) Expr) ← IO.mkRef {}

/-- Explicit cleanup for long-lived elaborator processes. -/
def clearCaches : IO Unit := finLiteralCache.set {}

/-- A literal Fin value carrying an ordinary checked decidability proof. -/
def finLiteral (n value : Nat) : MetaM Expr := do
  if value >= n then throwError "support/selector index outside Fin bound"
  if let some result := (← finLiteralCache.get)[(n, value)]? then
    return result
  let nExpr := mkNatLit n
  let valueExpr := mkNatLit value
  let lt ← mkLT valueExpr nExpr
  let hlt ← mkDecideProof lt
  let result ← instantiateMVars (mkApp3 (mkConst ``Fin.mk) nExpr valueExpr hlt)
  if result.hasMVar || result.hasFVar || result.hasLooseBVars || result.hasLevelParam then
    throwError "refusing to cache a non-closed Fin expression"
  finLiteralCache.modify fun cache => cache.insert (n, value) result
  return result

/-- Memoize one generator's literal Fin-valued support and its equality to the
actual quadSupport definition. Both declarations go through ordinary addDecl. -/
def ensureSupport (stem supportFn : Name)
    (data : Quartic.CertificateBinaryIO.SparseMetadata) (g : Nat) :
    MetaM (Expr × Expr × Expr) := do
  let a ← finLiteral data.supports.size g
  let valueName := stem ++ Name.mkSimple ("support_value_" ++ toString g)
  let eqName := stem ++ Name.mkSimple ("support_lookup_" ++ toString g)
  if !(← getEnv).contains valueName then
    let finType := mkApp (mkConst ``Fin) (mkNatLit data.dimension)
    let mut entries : Array Expr := #[]
    for j in data.supports[g]! do
      entries := entries.push (← finLiteral data.dimension j)
    let value ← mkListLit finType entries.toList
    addDecl (forceExpose := true) <| .defnDecl {
      name := valueName, levelParams := [],
      type := mkApp (mkConst ``List [.zero]) finType,
      value, hints := .regular 0, safety := .safe }
    modifyEnv (addNoncomputable · valueName)
    let rhs := mkConst valueName
    addDecl <| .thmDecl {
      name := eqName, levelParams := [],
      type := ← mkEq (mkApp (mkConst supportFn) a) rhs,
      value := ← mkEqRefl rhs }
  return (a, mkConst valueName, mkConst eqName)

/-- A checked naturalProduct lookup. The candidate literal is untrusted until
ordinary addDecl verifies the reflexivity proof against the actual table lookup.
Only the theorem is stored: the right side is already a small Nat literal. -/
def ensureProduct (stem productFn : Name)
    (data : Quartic.CertificateBinaryIO.SparseMetadata) (a b : Nat) :
    MetaM (Expr × Expr × Expr) := do
  if a >= data.dimension || b >= data.dimension then
    throwError "product index outside metadata dimensions"
  let k := a * data.dimension + b
  let eqName := stem ++ Name.mkSimple ("product_lookup_" ++ toString k)
  let rhs := mkNatLit ((data.productIndices[k]!).toNat)
  -- Reading the checked theorem's exact left side avoids rebuilding any Fin
  -- proof or re-running typeclass synthesis for repeated product occurrences.
  if let some info := (← getEnv).find? eqName then
    let some (_, lhs, _) := info.type.eq? | throwError "product memo is not an equality"
    return (rhs, mkConst eqName, lhs)
  let aFin ← finLiteral data.dimension a
  let bFin ← finLiteral data.dimension b
  let lhs := mkApp4 (mkConst ``mappedProduct) (mkNatLit data.dimension)
    (mkConst productFn) bFin aFin
  addDecl <| .thmDecl {
    name := eqName, levelParams := [],
    type := ← mkEq lhs rhs,
    value := ← mkEqRefl rhs }
  return (rhs, mkConst eqName, lhs)

/-- Map congruence built from checked product lookups, rather than reducing each
balanced product tree again. Immutable accumulators share their list tails. -/
def productsProof (stem productFn : Name)
    (data : Quartic.CertificateBinaryIO.SparseMetadata) (g m : Nat) :
    MetaM Expr := do
  let nat := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [.zero]) nat
  let cons := mkApp (mkConst ``List.cons [.zero]) nat
  let consCongr ← mkAppM ``congrArg₂ #[cons]
  let mut left := nil
  let mut right := nil
  let mut result ← mkEqRefl nil
  for j in (data.supports[g]!).reverse do
    let (value, hj, head) ← ensureProduct stem productFn data j m
    result := mkApp6 consCongr head value left right hj result
    left := mkApp2 cons head left
    right := mkApp2 cons value right
  return result

/-- Build exactly the old shape statement, using the actual definitions inferred
from naturalRow's namespace. No expensive Meta-level equality check is required:
addDecl of shape_i below checks the selector and product reflexivity proofs. -/
def shapeProof (stem rowFn : Name)
    (data : Quartic.CertificateBinaryIO.SparseMetadata) (i : Nat) (ys : Expr) :
    MetaM Expr := do
  if i >= data.rows.size then throwError "selector index outside metadata"
  let (g, m) := data.rows[i]!
  let owner := rowFn.getPrefix
  let select := mkConst (owner ++ `selectedRaw)
  let support := mkConst (owner ++ `quadSupport)
  let product := mkConst (owner ++ `naturalProduct)
  let (a, xs, hsupport) ← ensureSupport stem (owner ++ `quadSupport) data g
  let b ← finLiteral data.dimension m
  let gType := mkApp (mkConst ``Fin) (mkNatLit data.supports.size)
  let dType := mkApp (mkConst ``Fin) (mkNatLit data.dimension)
  let pair := mkApp4 (mkConst ``Prod.mk [.zero, .zero]) gType dType a b
  let hselect ← mkEqRefl pair
  let hproducts ← productsProof stem (owner ++ `naturalProduct) data g m
  return mkAppN (mkConst ``rowShapeOfMemo) #[
    mkNatLit data.supports.size, mkNatLit data.dimension,
    select, support, product, mkNatLit i, a, b, xs, ys,
    hselect, hsupport, hproducts]

syntax (name := supportLookups) "certify_support_lookups " ident
  " from " str " support_fn " ident : command

@[command_elab supportLookups] def elabSupportLookups : CommandElab := fun stx => do
  let `(certify_support_lookups $pref:ident from $directory:str
      support_fn $fn:ident) := stx | throwUnsupportedSyntax
  let data ← Quartic.CertificateBinaryIO.readSparseMetadataCached directory.getString
  let stem := (← getCurrNamespace) ++ pref.getId
  for g in [:data.supports.size] do
    liftTermElabM do
      let _ ← ensureSupport stem fn.getId data g
  logInfo m!"Kernel checked {data.supports.size} generator support equalities."

/-- Precheck a flat interval of the product table. Intervals can be split among
independent modules with the same stem, then imported by the row modules. -/
syntax (name := productLookups) "certify_product_lookups " ident
  " from " str " product_fn " ident " start_index " num " lookup_count " num : command

@[command_elab productLookups] def elabProductLookups : CommandElab := fun stx => do
  let pref := stx[1].getId
  let some directory := stx[3].isStrLit? | throwUnsupportedSyntax
  let fn := stx[5].getId
  let some start := stx[7].isNatLit? | throwUnsupportedSyntax
  let some count := stx[9].isNatLit? | throwUnsupportedSyntax
  let data ← Quartic.CertificateBinaryIO.readSparseMetadataCached directory
  if start + count > data.dimension * data.dimension then
    throwError "product memo interval outside table"
  let stem := (← getCurrNamespace) ++ pref
  for k in [start:start + count] do
    liftTermElabM do
      let _ ← ensureProduct stem fn data (k / data.dimension) (k % data.dimension)
  logInfo m!"Kernel checked {count} product lookup equalities from {start}."

/-- Optional sample preparation: precheck only products used by a row interval.
This allows timing warm row checking separately from its reusable memo setup. -/
syntax (name := rowProductLookups) "certify_row_product_lookups " ident
  " from " str " product_fn " ident " start_index " num " row_count " num : command

@[command_elab rowProductLookups] def elabRowProductLookups : CommandElab := fun stx => do
  let pref := stx[1].getId
  let some directory := stx[3].isStrLit? | throwUnsupportedSyntax
  let fn := stx[5].getId
  let some start := stx[7].isNatLit? | throwUnsupportedSyntax
  let some count := stx[9].isNatLit? | throwUnsupportedSyntax
  let data ← Quartic.CertificateBinaryIO.readSparseMetadataCached directory
  if start + count > data.rows.size then
    throwError "row product memo interval outside metadata"
  let stem := (← getCurrNamespace) ++ pref
  for i in [start:start + count] do
    let (g, m) := data.rows[i]!
    for j in data.supports[g]! do
      liftTermElabM do
        let _ ← ensureProduct stem fn data j m
  logInfo m!"Kernel checked products used by {count} rows from {start}."

end
end Quartic.FiniteEndpointShapeMemo
