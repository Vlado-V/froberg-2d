import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata28Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n28/quadCodes.bin" nrows 406 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n28/quarticCodes.bin" nrows 31465 nwords 1
load_packed_tree products from "certificates/finite/n28/products.bin" nrows 164836 nwords 1
load_packed_tree coefficients from "certificates/finite/n28/coefficients.bin" nrows 87 nwords 7
load_packed_tree selectedCodes from "certificates/finite/n28/selected.bin" nrows 31465 nwords 1

def digit (code place : ℕ) : Fin 28 := ⟨code/place%28,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 406) : List (Fin 28) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 28]
def vars4 (i : Fin 31465) : List (Fin 28) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 28,
   digit (quarticCodes.get i.val) 784,digit (quarticCodes.get i.val) 21952]
def exponent2 (i : Fin 406) : Fin 28 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 31465) : Fin 28 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 87) : List (Fin 406) :=
  (List.finRange 406).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 87 × Fin 406 :=
  (⟨selectedGenerator i % 87,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 406,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 31465) : Fin 87 × Fin 406 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*406+j)
def productIndex (i j : Fin 406) : Fin 31465 :=
  ⟨naturalProduct i.val j.val % 31465,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 31465) : List (Fin 31465) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 406) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 31465) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata28Data
