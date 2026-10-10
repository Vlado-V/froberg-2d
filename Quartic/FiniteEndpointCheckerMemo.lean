module

public import Quartic.CertificateBinaryIO

public import Quartic.FiniteEndpointCheckerLoad
public import Quartic.FiniteEndpointShapeMemo

@[expose] public section

/-! A proof-producing sparse-row elaborator using one scalar XOR fold. Every generated equality is submitted
as an ordinary theorem to `addDecl`; no evaluator result is trusted as a proof. -/
namespace Quartic.FiniteEndpointCheckerMemo
open Quartic.FiniteEndpointChecker
open Quartic.FiniteEndpointShapeMemo

/-- Keep one scalar function head throughout the checked fold. -/
def RowTerm {d : Nat} (inv : Nat → Nat) (product : Nat → Nat → Nat)
    (b j : Fin d) : Nat := inv (mappedProduct product b j)

/-- Keep the scalar function head identical to xorMapStep's premise, so the
kernel need not unfold an inverse lookup while matching that premise. -/
theorem rowTermEq {d : Nat} (inv : Nat → Nat) (product : Nat → Nat → Nat)
    (b j : Fin d) (productIndex value : Nat)
    (hproduct : mappedProduct product b j = productIndex)
    (hinverse : inv productIndex = value) :
    RowTerm inv product b j = value := by
  unfold RowTerm
  exact (congrArg inv hproduct).trans hinverse

universe u

/-- The proof state has one support tail and one scalar XOR expression. -/
theorem xorMapStep {α : Type u} (f : α → Nat) (j : α) (xs : List α) (x t : Nat)
    (hx : f j = x) (ht : xorSum (xs.map f) = t) :
    xorSum ((j :: xs).map f) = Nat.xor x t := by
  change Nat.xor (f j) (xorSum (xs.map f)) = Nat.xor x t
  exact congrArg₂ Nat.xor hx ht

/-- Transport the fused fold to the actual selected-generator row. All selector
and support substitutions remain proved equalities. -/
theorem rowEquation {g d : Nat}
    (select : Nat → Fin g × Fin d) (support : Fin g → List (Fin d))
    (product : Nat → Nat → Nat) (inv : Nat → Nat) (i : Nat)
    (a : Fin g) (b : Fin d) (xs : List (Fin d)) (rhs : Nat)
    (hselect : select i = (a, b)) (hsupport : support a = xs)
    (hfold : xorSum (xs.map (RowTerm inv product b)) = rhs) :
    xorSum (((support (select i).1).map
      (fun j => product j.val (select i).2.val)).map inv) = rhs := by
  rw [hselect, hsupport, List.map_map]
  exact hfold

open Lean Meta Elab Command
meta section

def u64 (a : ByteArray) (o : Nat) : UInt64 :=
  (a.get! (o+7)).toUInt64 <<< 56 ||| (a.get! (o+6)).toUInt64 <<< 48 |||
  (a.get! (o+5)).toUInt64 <<< 40 ||| (a.get! (o+4)).toUInt64 <<< 32 |||
  (a.get! (o+3)).toUInt64 <<< 24 ||| (a.get! (o+2)).toUInt64 <<< 16 |||
  (a.get! (o+1)).toUInt64 <<< 8 ||| (a.get! o).toUInt64
def u32 (a : ByteArray) (o : Nat) : Nat :=
  (a.get! o).toNat + 256*(a.get! (o+1)).toNat +
  65536*(a.get! (o+2)).toNat + 16777216*(a.get! (o+3)).toNat

def ensureLookup (stem fn : Name) (loadBytes : IO ByteArray) (nw j : Nat) : MetaM (Expr × Expr) := do
  let valName := stem ++ Name.mkSimple ("value_" ++ toString j)
  let eqName := stem ++ Name.mkSimple ("lookup_" ++ toString j)
  if !(← getEnv).contains valName then
    let bytes ← loadBytes
    if (j+1)*nw*8 > bytes.size then throwError "inverse index outside binary file"
    let mut val : Nat := 0
    for rev in [:nw] do
      val := val <<< 64 ||| (u64 bytes ((j*nw+(nw-1-rev))*8)).toNat
    addDecl (forceExpose := true) <| .defnDecl {
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

/-- Nat transitivity with explicit arguments, so constructing the certificate
never asks Meta to normalize the giant packed scalar expression. -/
def scalarTransNat (a b c hab hbc : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [.succ .zero]) (mkConst ``Nat) a b c hab hbc

/-- Fused proof of the SAME row_i theorem. No mapped Nat lists, cons-congruence
chain, or separate shape_i declaration is built. All untrusted data is checked
through the existing product/support/inverse equalities and final addDecl. -/
def certifyRow (stem invFn rowFn : Name) (loadInvBytes : IO ByteArray)
    (nw i : Nat) (indices : Array Nat)
    (metadata : Quartic.CertificateBinaryIO.SparseMetadata) : MetaM Unit := do
  if i >= metadata.rows.size then throwError "selector index outside metadata"
  let (g, m) := metadata.rows[i]!
  if g >= metadata.supports.size then throwError "support index outside metadata"
  let supportIndices := metadata.supports[g]!
  if supportIndices.size != indices.size then
    throwError "sparse row differs from metadata support length"
  let d := metadata.dimension
  let dExpr := mkNatLit d
  let gExpr := mkNatLit metadata.supports.size
  let nat := mkConst ``Nat
  let finType := mkApp (mkConst ``Fin) dExpr
  let owner := rowFn.getPrefix
  let select := mkConst (owner ++ `selectedRaw)
  let support := mkConst (owner ++ `quadSupport)
  let productName := owner ++ `naturalProduct
  let product := mkConst productName
  let inv := mkConst invFn
  let (a, _, hsupport) ← Quartic.FiniteEndpointShapeMemo.ensureSupport
    stem (owner ++ `quadSupport) metadata g
  let b ← Quartic.FiniteEndpointShapeMemo.finLiteral d m
  let termFn := mkApp4 (mkConst ``RowTerm) dExpr inv product b
  -- xorMapStep's fixed α/f arguments are supplied once. Every loop iteration
  -- supplies j, xs, x, t, hx, ht directly, with no mkAppM/unification.
  let step := mkApp2 (mkConst ``xorMapStep [.zero]) finType termFn
  let nil := mkApp (mkConst ``List.nil [.zero]) finType
  let cons := mkApp (mkConst ``List.cons [.zero]) finType
  let mut supportTail := nil
  let mut scalar := mkNatLit 0
  let mut hfold ← mkEqRefl scalar
  for rev in [:supportIndices.size] do
    let offset := supportIndices.size - 1 - rev
    let j := supportIndices[offset]!
    let jFin ← Quartic.FiniteEndpointShapeMemo.finLiteral d j
    let (productIndex, hproduct, _actualProduct) ←
      Quartic.FiniteEndpointShapeMemo.ensureProduct stem productName metadata j m
    let k := (metadata.productIndices[j * d + m]!).toNat
    -- This is a consistency guard for the existing sparse-data input. It is
    -- not trusted as a theorem: product/inverse declarations still check it.
    if k != indices[offset]! then throwError "sparse row differs from product metadata"
    let (value, hinverse) ← ensureLookup stem invFn loadInvBytes nw k
    let hterm := mkAppN (mkConst ``rowTermEq)
      #[dExpr, inv, product, b, jFin, productIndex, value, hproduct, hinverse]
    hfold := mkApp6 step jFin supportTail value scalar hterm hfold
    supportTail := mkApp2 cons jFin supportTail
    scalar := mkApp2 (mkConst ``Nat.xor) value scalar
  let mapTerm ← mkAppM ``List.map #[termFn]
  let foldLhs := mkApp (mkConst ``Quartic.FiniteEndpointChecker.xorSum)
    (mkApp mapTerm supportTail)
  -- Keep the power symbolic. The final kernel equality checks its value; the
  -- elaborator does not manufacture a gigantic numeral in the theorem type.
  let expected := mkApp2 (mkConst ``Nat.pow) (mkNatLit 2) (mkNatLit i)
  let hfoldExpected := scalarTransNat foldLhs scalar expected hfold (← mkEqRefl expected)
  let gType := mkApp (mkConst ``Fin) gExpr
  let pair := mkApp4 (mkConst ``Prod.mk [.zero, .zero]) gType finType a b
  let hselect ← mkEqRefl pair
  let proof := mkAppN (mkConst ``rowEquation)
    #[gExpr, dExpr, select, support, product, inv, mkNatLit i, a, b,
      supportTail, expected, hselect, hsupport, hfoldExpected]
  let source := mkApp (mkConst rowFn) (mkNatLit i)
  let mapInv ← mkAppM ``List.map #[inv]
  let lhs := mkApp (mkConst ``Quartic.FiniteEndpointChecker.xorSum) (mkApp mapInv source)
  let type ← mkEq lhs expected
  let name := stem ++ Name.mkSimple ("row_" ++ toString i)
  addDecl <| .thmDecl {name, levelParams := [], type, value := proof}

syntax (name := memoLookups) "certify_inverse_lookups " ident " from " str
  " inverse_fn " ident " nrows " num " nwords " num : command

@[command_elab memoLookups] def elabMemoLookups : CommandElab := fun stx => do
  let `(certify_inverse_lookups $pref:ident from $path:str inverse_fn $fn:ident
      nrows $nr:num nwords $nw:num) := stx | throwUnsupportedSyntax
  let bytes ← Quartic.CertificateBinaryIO.readBinaryOrPartsCached path.getString
  let stem := (← getCurrNamespace) ++ pref.getId
  for j in [:nr.getNat] do
    liftTermElabM do
      let _ ← ensureLookup stem fn.getId (pure bytes) nw.getNat j
  logInfo m!"Kernel checked {nr.getNat} inverse lookup equalities."

syntax (name := memoRows) "certify_sparse_rows " ident " from " str
  " inverse_file " str " inverse_fn " ident " row_fn " ident
  " nwords " num " start_index " num " row_count " num : command

@[command_elab memoRows] def elabMemoRows : CommandElab := fun stx => do
  let `(certify_sparse_rows $pref:ident from $sparsePath:str
      inverse_file $invPath:str inverse_fn $invFn:ident row_fn $rowFn:ident
      nwords $nw:num start_index $start:num row_count $count:num) := stx | throwUnsupportedSyntax
  let rows ← Quartic.CertificateBinaryIO.readSparseRowsCached
    sparsePath.getString start.getNat count.getNat
  let metadata ← Quartic.CertificateBinaryIO.readSparseMetadataCached
    ((System.FilePath.mk sparsePath.getString).parent.getD ".")
  let loadInvBytes := Quartic.CertificateBinaryIO.readBinaryOrPartsCached invPath.getString
  let stem := (← getCurrNamespace) ++ pref.getId
  for offset in [:count.getNat] do
    let i := start.getNat + offset
    let values := rows[offset]!
    liftTermElabM do
      certifyRow stem invFn.getId rowFn.getId loadInvBytes nw.getNat i values metadata
  logInfo m!"Kernel checked {count.getNat} sparse rows from index {start.getNat}, with memoized lookup equalities."

end
end Quartic.FiniteEndpointCheckerMemo
