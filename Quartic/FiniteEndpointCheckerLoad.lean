import Lean
import Quartic.FiniteEndpointChecker

/-! Untrusted binary-data reification only. Generated declarations contain ordinary
Nat literals. Inverse equations are proved separately by Lean's kernel. -/
namespace Quartic.FiniteEndpointCheckerLoad
open Lean Meta Elab Command
inductive NatTree where
  | leaf : Nat → NatTree
  | node : Nat → NatTree → NatTree → NatTree

def NatTree.get : NatTree → Nat → Nat
  | .leaf x, _ => x
  | .node pivot l r, i => if i < pivot then l.get i else r.get i

meta section

private def readU64 (buf : ByteArray) (offset : Nat) : UInt64 :=
  (buf.get! (offset+7)).toUInt64 <<< 56 |||
  (buf.get! (offset+6)).toUInt64 <<< 48 |||
  (buf.get! (offset+5)).toUInt64 <<< 40 |||
  (buf.get! (offset+4)).toUInt64 <<< 32 |||
  (buf.get! (offset+3)).toUInt64 <<< 24 |||
  (buf.get! (offset+2)).toUInt64 <<< 16 |||
  (buf.get! (offset+1)).toUInt64 <<< 8 |||
  (buf.get! offset).toUInt64

private def readU32 (buf : ByteArray) (offset : Nat) : Nat :=
  (buf.get! offset).toNat + 256*(buf.get! (offset+1)).toNat +
    65536*(buf.get! (offset+2)).toNat + 16777216*(buf.get! (offset+3)).toNat

private def addData (name : Name) (type value : Expr) : MetaM Unit := do
  addDecl <| .defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}
  modifyEnv (addNoncomputable · name)

private partial def buildTree (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo+1 then mkApp (mkConst ``NatTree.leaf) xs[lo]!
  else
    let mid := (lo+hi)/2
    mkApp3 (mkConst ``NatTree.node) (mkNatLit mid) (buildTree xs lo mid) (buildTree xs mid hi)


syntax (name := packedRows) "load_packed_rows " ident " from " str " nrows " num " nwords " num : command

@[command_elab packedRows] def elabPackedRows : CommandElab := fun stx => do
  let `(load_packed_rows $name:ident from $path:str nrows $nr:num nwords $nw:num) := stx | throwUnsupportedSyntax
  let buf ← IO.FS.readBinFile path.getString
  let rowCount := nr.getNat
  let wordCount := nw.getNat
  if rowCount*wordCount*8 > buf.size then throwError "packed file too short"
  let mut exprs : Array Expr := #[]
  for i in [:rowCount] do
    let mut val : Nat := 0
    for rev in [:wordCount] do
      let j := wordCount-1-rev
      val := val <<< 64 ||| (readU64 buf ((i*wordCount+j)*8)).toNat
    exprs := exprs.push (mkNatLit val)
  let fullname := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let value ← mkArrayLit (mkConst ``Nat) exprs.toList
    addData fullname (mkApp (mkConst ``Array [.zero]) (mkConst ``Nat)) value
  logInfo m!"Reified {rowCount} packed Nat rows ({rowCount*wordCount*8} bytes); no rank assertion."

syntax (name := packedTree) "load_packed_tree " ident " from " str " nrows " num " nwords " num : command

@[command_elab packedTree] def elabPackedTree : CommandElab := fun stx => do
  let `(load_packed_tree $name:ident from $path:str nrows $nr:num nwords $nw:num) := stx | throwUnsupportedSyntax
  let buf ← IO.FS.readBinFile path.getString
  let rowCount := nr.getNat
  let wordCount := nw.getNat
  if rowCount == 0 || rowCount*wordCount*8 > buf.size then throwError "invalid packed file dimensions"
  let mut exprs : Array Expr := #[]
  for i in [:rowCount] do
    let mut val : Nat := 0
    for rev in [:wordCount] do
      let j := wordCount-1-rev
      val := val <<< 64 ||| (readU64 buf ((i*wordCount+j)*8)).toNat
    exprs := exprs.push (mkNatLit val)
  let fullname := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    addData fullname (mkConst ``NatTree) (buildTree exprs 0 exprs.size)
  logInfo m!"Reified {rowCount} packed Nat rows as a balanced tree; no rank assertion."

syntax (name := sparseRows) "load_sparse_rows " ident " from " str " nrows " num : command

@[command_elab sparseRows] def elabSparseRows : CommandElab := fun stx => do
  let `(load_sparse_rows $name:ident from $path:str nrows $nr:num) := stx | throwUnsupportedSyntax
  let buf ← IO.FS.readBinFile path.getString
  let mut offset := 0
  let mut rowLists : Array (List Expr) := #[]
  for _ in [:nr.getNat] do
    if offset+4 > buf.size then throwError "sparse file too short"
    let n := readU32 buf offset
    offset := offset+4
    if offset+4*n > buf.size then throwError "sparse file too short"
    let mut row : Array Expr := #[]
    for j in [:n] do row := row.push (mkNatLit (readU32 buf (offset+4*j)))
    offset := offset+4*n
    rowLists := rowLists.push row.toList
  let fullname := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let mut vals := []
    for r in rowLists.reverse do vals := (← mkListLit (mkConst ``Nat) r)::vals
    let listNat := mkApp (mkConst ``List [.zero]) (mkConst ``Nat)
    let value ← mkArrayLit listNat vals
    addData fullname (mkApp (mkConst ``Array [.zero]) listNat) value
  logInfo m!"Reified {nr.getNat} sparse Nat rows; no rank assertion."

end
end Quartic.FiniteEndpointCheckerLoad
