import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata26Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n26/quadCodes.bin" nrows 351 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n26/quarticCodes.bin" nrows 23751 nwords 1
load_packed_tree products from "certificates/finite/n26/products.bin" nrows 123201 nwords 1
load_packed_tree coefficients from "certificates/finite/n26/coefficients.bin" nrows 76 nwords 6
load_packed_tree selectedCodes from "certificates/finite/n26/selected.bin" nrows 23751 nwords 1

def digit (code place : ℕ) : Fin 26 := ⟨code/place%26,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 351) : List (Fin 26) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 26]
def vars4 (i : Fin 23751) : List (Fin 26) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 26,
   digit (quarticCodes.get i.val) 676,digit (quarticCodes.get i.val) 17576]
def exponent2 (i : Fin 351) : Fin 26 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 23751) : Fin 26 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 76) : List (Fin 351) :=
  (List.finRange 351).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 76 × Fin 351 :=
  (⟨selectedGenerator i % 76,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 351,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 23751) : Fin 76 × Fin 351 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*351+j)
def productIndex (i j : Fin 351) : Fin 23751 :=
  ⟨naturalProduct i.val j.val % 23751,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 23751) : List (Fin 23751) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 351) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 23751) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata26Data
