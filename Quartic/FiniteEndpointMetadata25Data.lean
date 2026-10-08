import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata25Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n25/quadCodes.bin" nrows 325 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n25/quarticCodes.bin" nrows 20475 nwords 1
load_packed_tree products from "certificates/finite/n25/products.bin" nrows 105625 nwords 1
load_packed_tree coefficients from "certificates/finite/n25/coefficients.bin" nrows 71 nwords 6
load_packed_tree selectedCodes from "certificates/finite/n25/selected.bin" nrows 20475 nwords 1

def digit (code place : ℕ) : Fin 25 := ⟨code/place%25,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 325) : List (Fin 25) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 25]
def vars4 (i : Fin 20475) : List (Fin 25) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 25,
   digit (quarticCodes.get i.val) 625,digit (quarticCodes.get i.val) 15625]
def exponent2 (i : Fin 325) : Fin 25 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 20475) : Fin 25 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 71) : List (Fin 325) :=
  (List.finRange 325).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 71 × Fin 325 :=
  (⟨selectedGenerator i % 71,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 325,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 20475) : Fin 71 × Fin 325 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*325+j)
def productIndex (i j : Fin 325) : Fin 20475 :=
  ⟨naturalProduct i.val j.val % 20475,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 20475) : List (Fin 20475) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 325) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 20475) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata25Data
