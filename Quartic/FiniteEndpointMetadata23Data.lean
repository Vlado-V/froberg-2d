import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata23Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n23/quadCodes.bin" nrows 276 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n23/quarticCodes.bin" nrows 14950 nwords 1
load_packed_tree products from "certificates/finite/n23/products.bin" nrows 76176 nwords 1
load_packed_tree coefficients from "certificates/finite/n23/coefficients.bin" nrows 61 nwords 5
load_packed_tree selectedCodes from "certificates/finite/n23/selected.bin" nrows 14950 nwords 1

def digit (code place : ℕ) : Fin 23 := ⟨code/place%23,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 276) : List (Fin 23) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 23]
def vars4 (i : Fin 14950) : List (Fin 23) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 23,
   digit (quarticCodes.get i.val) 529,digit (quarticCodes.get i.val) 12167]
def exponent2 (i : Fin 276) : Fin 23 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 14950) : Fin 23 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 61) : List (Fin 276) :=
  (List.finRange 276).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 61 × Fin 276 :=
  (⟨selectedGenerator i % 61,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 276,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 14950) : Fin 61 × Fin 276 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*276+j)
def productIndex (i j : Fin 276) : Fin 14950 :=
  ⟨naturalProduct i.val j.val % 14950,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 14950) : List (Fin 14950) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 276) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 14950) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata23Data
