module

public import Lean

@[expose] public section

/-!
Untrusted certificate-data IO. These helpers reconstruct bytes, not proofs.
The existing proof-producing certificate checker must still verify every row.
No Python process, network access, or generated file is needed by these helpers.
-/

namespace Quartic.CertificateBinaryIO
meta section

def readU64 (bytes : ByteArray) (offset : Nat) : UInt64 :=
  (bytes.get! (offset + 7)).toUInt64 <<< 56 |||
  (bytes.get! (offset + 6)).toUInt64 <<< 48 |||
  (bytes.get! (offset + 5)).toUInt64 <<< 40 |||
  (bytes.get! (offset + 4)).toUInt64 <<< 32 |||
  (bytes.get! (offset + 3)).toUInt64 <<< 24 |||
  (bytes.get! (offset + 2)).toUInt64 <<< 16 |||
  (bytes.get! (offset + 1)).toUInt64 <<< 8 |||
  (bytes.get! offset).toUInt64

def pushU32 (bytes : ByteArray) (value : UInt32) : ByteArray :=
  (((bytes.push value.toUInt8).push (value >>> 8).toUInt8).push
    (value >>> 16).toUInt8).push (value >>> 24).toUInt8

/-- Reconstruct the exact little-endian sparse-row format from polynomial
metadata. Supports stay in increasing quadratic-monomial order, with no sorting
or deduplication of the resulting product indices. Packed selected indices use
the same low/high 32-bit extraction and modulo conventions as the row definitions. -/
def reconstructSparseBytes (quadCodes coefficients products selected : ByteArray) :
    Except String ByteArray := do
  if quadCodes.size % 8 != 0 then throw "quadCodes.bin is not a sequence of 64-bit words"
  let dimension := quadCodes.size / 8
  if dimension == 0 then throw "empty quadratic basis"
  let width := ((dimension + 63) / 64) * 8
  if coefficients.size % width != 0 then throw "invalid coefficient dimensions"
  let generatorCount := coefficients.size / width
  if generatorCount == 0 then throw "empty coefficient family"
  if products.size != dimension * dimension * 8 then
    throw "invalid multiplication table dimensions"
  if selected.size % 8 != 0 then throw "selected.bin is not a sequence of 64-bit words"
  let mut supports : Array (Array Nat) := Array.emptyWithCapacity generatorCount
  for i in [:generatorCount] do
    let mut support : Array Nat := #[]
    for j in [:dimension] do
      let word := readU64 coefficients (i * width + (j / 64) * 8)
      if word &&& ((1 : UInt64) <<< (j % 64).toUInt64) != 0 then
        support := support.push j
    if support.size >= 2^32 then throw "sparse row length exceeds 32-bit format"
    supports := supports.push support
  let mut productIndices : Array UInt32 := Array.emptyWithCapacity (dimension * dimension)
  for j in [:dimension * dimension] do
    let value := readU64 products (j * 8)
    if value.toNat >= 2^32 then throw "product index exceeds 32-bit sparse format"
    productIndices := productIndices.push value.toUInt32
  let rowCount := selected.size / 8
  let mut rows : Array (Nat × Nat) := Array.emptyWithCapacity rowCount
  let mut byteCount := 0
  for i in [:rowCount] do
    let code := readU64 selected (i * 8)
    let generator := (code &&& 0xffffffff).toNat % generatorCount
    let multiplier := (code >>> 32).toNat % dimension
    rows := rows.push (generator, multiplier)
    byteCount := byteCount + 4 * (supports[generator]!.size + 1)
  let mut result := ByteArray.emptyWithCapacity byteCount
  for (generator, multiplier) in rows do
    let support := supports[generator]!
    result := pushU32 result support.size.toUInt32
    for j in support do
      result := pushU32 result productIndices[j * dimension + multiplier]!
  return result

/-- Load only the four retained metadata files and reconstruct sparse bytes in memory. -/
def reconstructSparse (directory : System.FilePath) : IO ByteArray := do
  let quadCodes ← IO.FS.readBinFile (directory / "quadCodes.bin")
  let coefficients ← IO.FS.readBinFile (directory / "coefficients.bin")
  let products ← IO.FS.readBinFile (directory / "products.bin")
  let selected ← IO.FS.readBinFile (directory / "selected.bin")
  match reconstructSparseBytes quadCodes coefficients products selected with
  | .ok bytes => return bytes
  | .error message => throw <| IO.userError s!"{directory}: {message}"

/-- Concatenate an explicit ordered list of chunks. No directory enumeration or
lexicographic/numeric sorting determines the order. -/
def readOrderedParts (parts : Array System.FilePath) : IO ByteArray := do
  if parts.isEmpty then throw <| IO.userError "empty certificate chunk list"
  let mut result := ByteArray.empty
  for part in parts do
    let bytes ← IO.FS.readBinFile part
    result := result ++ bytes
  return result

/-- Read a file if present; otherwise read its `.parts/manifest`. The UTF-8
manifest lists chunk basenames in exact concatenation order, one per line.
Blank lines are ignored; duplicate names and names containing directories are
rejected. Missing files are IO errors. The original file takes precedence. -/
def readBinaryOrParts (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then return ← IO.FS.readBinFile path
  let directory := path.addExtension "parts"
  let manifest ← IO.FS.readFile (directory / "manifest")
  let mut names : Array String := #[]
  let mut parts : Array System.FilePath := #[]
  for line in manifest.splitOn "\n" do
    let name := line.trimAscii.toString
    if name.isEmpty then continue
    if name == "." || name == ".." || name.contains '/' || name.contains '\\' then
      throw <| IO.userError s!"{directory}: invalid chunk basename {name}"
    if names.contains name then
      throw <| IO.userError s!"{directory}: duplicate chunk {name}"
    names := names.push name
    parts := parts.push (directory / name)
  readOrderedParts parts

/-- Compatibility helper for existing `sparse.bin` path arguments. -/
def readSparseOrReconstruct (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then return ← IO.FS.readBinFile path
  if path.fileName != some "sparse.bin" then
    throw <| IO.userError s!"cannot reconstruct non-sparse certificate path {path}"
  reconstructSparse (path.parent.getD ".")

initialize binaryCache : IO.Ref (Array (System.FilePath × ByteArray)) ← IO.mkRef #[]
initialize sparseCache : IO.Ref (Array (System.FilePath × ByteArray)) ← IO.mkRef #[]

def readCached (cache : IO.Ref (Array (System.FilePath × ByteArray)))
    (reader : System.FilePath → IO ByteArray) (path : System.FilePath) : IO ByteArray := do
  for (cachedPath, bytes) in ← cache.get do
    if cachedPath == path then return bytes
  let bytes ← reader path
  cache.modify (·.push (path, bytes))
  return bytes

/-- Cache successful reads per process and exact path. Certificate inputs must
remain fixed during a build; call `clearCaches` after intentionally changing them.
Errors are not cached. The proof-producing checker still checks every use. -/
def readBinaryOrPartsCached (path : System.FilePath) : IO ByteArray :=
  readCached binaryCache readBinaryOrParts path

/-- Avoid reconstructing the same sparse data for each row command in a module. -/
def readSparseOrReconstructCached (path : System.FilePath) : IO ByteArray :=
  readCached sparseCache readSparseOrReconstruct path

/-- Discard both process-local caches, for tests or explicitly changed inputs. -/
def clearCaches : IO Unit := do
  binaryCache.set #[]
  sparseCache.set #[]

end
end Quartic.CertificateBinaryIO
