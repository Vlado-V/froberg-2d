import Quartic.FiniteEndpointCheckerLoad

/-! A proof-producing sparse-row elaborator. Every generated equality is submitted
as an ordinary theorem to `addDecl`; no evaluator result is trusted as a proof. -/
namespace Quartic.FiniteEndpointCheckerMemo
open Lean Meta Elab Command
meta section

private def u64 (a : ByteArray) (o : Nat) : UInt64 :=
  (a.get! (o+7)).toUInt64 <<< 56 ||| (a.get! (o+6)).toUInt64 <<< 48 |||
  (a.get! (o+5)).toUInt64 <<< 40 ||| (a.get! (o+4)).toUInt64 <<< 32 |||
  (a.get! (o+3)).toUInt64 <<< 24 ||| (a.get! (o+2)).toUInt64 <<< 16 |||
  (a.get! (o+1)).toUInt64 <<< 8 ||| (a.get! o).toUInt64
private def u32 (a : ByteArray) (o : Nat) : Nat :=
  (a.get! o).toNat + 256*(a.get! (o+1)).toNat +
  65536*(a.get! (o+2)).toNat + 16777216*(a.get! (o+3)).toNat

private def ensureLookup (stem fn : Name) (bytes : ByteArray) (nw j : Nat) : MetaM (Expr × Expr) := do
  let valName := stem ++ Name.mkSimple ("value_" ++ toString j)
  let eqName := stem ++ Name.mkSimple ("lookup_" ++ toString j)
  if !(← getEnv).contains valName then
    if (j+1)*nw*8 > bytes.size then throwError "inverse index outside binary file"
    let mut val : Nat := 0
    for rev in [:nw] do
      val := val <<< 64 ||| (u64 bytes ((j*nw+(nw-1-rev))*8)).toNat
    addDecl <| .defnDecl {
      name := valName
      levelParams := []
      type := mkConst ``Nat
      value := mkNatLit val
      hints := .regular 0
      safety := .safe }
    modifyEnv (addNoncomputable · valName)
    let rhs := mkConst valName
    let lhs := mkApp (mkConst fn) (mkNatLit j)
    addDecl <| .thmDecl {
      name := eqName
      levelParams := []
      type := ← mkEq lhs rhs
      value := ← mkEqRefl rhs }
  return (mkConst valName,mkConst eqName)

private def certifyRow (stem invFn rowFn : Name) (invBytes : ByteArray)
    (nw i : Nat) (indices : Array Nat) : MetaM Unit := do
  let nat := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [.zero]) nat
  let cons := mkApp (mkConst ``List.cons [.zero]) nat
  let mut listEq ← mkEqRefl nil
  for j in indices.reverse do
    let (_,hj) ← ensureLookup stem invFn invBytes nw j
    listEq ← mkAppM ``congrArg₂ #[cons,hj,listEq]
  let source := mkApp (mkConst rowFn) (mkNatLit i)
  let literalList ← mkListLit nat (indices.toList.map mkNatLit)
  let shapeName := stem ++ Name.mkSimple ("shape_" ++ toString i)
  addDecl <| .thmDecl {
    name := shapeName
    levelParams := []
    type := ← mkEq source literalList
    value := ← mkEqRefl literalList }
  let mapFn ← mkAppM ``List.map #[mkConst invFn]
  let shapeMap ← mkAppM ``congrArg #[mapFn,mkConst shapeName]
  let mappedEq ← mkAppM ``Eq.trans #[shapeMap,listEq]
  let xor := mkConst ``Quartic.FiniteEndpointChecker.xorSum
  let hx ← mkAppM ``congrArg #[xor,mappedEq]
  let rhs := mkNatLit (2^i)
  let proof ← mkAppM ``Eq.trans #[hx,← mkEqRefl rhs]
  let mapped ← mkAppM ``List.map #[mkConst invFn,source]
  let type ← mkEq (mkApp xor mapped) rhs
  let name := stem ++ Name.mkSimple ("row_" ++ toString i)
  addDecl <| .thmDecl {name,levelParams := [], type,value := proof}

syntax (name := memoLookups) "certify_inverse_lookups " ident " from " str
  " inverse_fn " ident " nrows " num " nwords " num : command

@[command_elab memoLookups] def elabMemoLookups : CommandElab := fun stx => do
  let `(certify_inverse_lookups $pref:ident from $path:str inverse_fn $fn:ident
      nrows $nr:num nwords $nw:num) := stx | throwUnsupportedSyntax
  let bytes ← IO.FS.readBinFile path.getString
  let stem := (← getCurrNamespace) ++ pref.getId
  for j in [:nr.getNat] do
    liftTermElabM do
      let _ ← ensureLookup stem fn.getId bytes nw.getNat j
  logInfo m!"Kernel checked {nr.getNat} inverse lookup equalities."

syntax (name := memoRows) "certify_sparse_rows " ident " from " str
  " inverse_file " str " inverse_fn " ident " row_fn " ident
  " nwords " num " start_index " num " row_count " num : command

@[command_elab memoRows] def elabMemoRows : CommandElab := fun stx => do
  let `(certify_sparse_rows $pref:ident from $sparsePath:str
      inverse_file $invPath:str inverse_fn $invFn:ident row_fn $rowFn:ident
      nwords $nw:num start_index $start:num row_count $count:num) := stx | throwUnsupportedSyntax
  let sparseBytes ← IO.FS.readBinFile sparsePath.getString
  let invBytes ← IO.FS.readBinFile invPath.getString
  let stem := (← getCurrNamespace) ++ pref.getId
  let mut offset := 0
  for i in [:start.getNat+count.getNat] do
    if offset+4 > sparseBytes.size then throwError "sparse file too short"
    let len := u32 sparseBytes offset
    offset := offset+4
    if offset+4*len > sparseBytes.size then throwError "sparse file too short"
    if start.getNat ≤ i then
      let mut values : Array Nat := #[]
      for j in [:len] do values := values.push (u32 sparseBytes (offset+4*j))
      liftTermElabM do
        certifyRow stem invFn.getId rowFn.getId invBytes nw.getNat i values
    offset := offset+4*len
  logInfo m!"Kernel checked {count.getNat} sparse rows from index {start.getNat}, with memoized lookup equalities."

end
end Quartic.FiniteEndpointCheckerMemo
