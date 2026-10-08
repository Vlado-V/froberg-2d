import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata22Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n22/quadCodes.bin" nrows 253 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n22/quarticCodes.bin" nrows 12650 nwords 1
load_packed_tree products from "certificates/finite/n22/products.bin" nrows 64009 nwords 1
load_packed_tree coefficients from "certificates/finite/n22/coefficients.bin" nrows 57 nwords 4
load_packed_tree selectedCodes from "certificates/finite/n22/selected.bin" nrows 12650 nwords 1

def digit (code place : ℕ) : Fin 22 := ⟨code/place%22,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 253) : List (Fin 22) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 22]
def vars4 (i : Fin 12650) : List (Fin 22) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 22,
   digit (quarticCodes.get i.val) 484,digit (quarticCodes.get i.val) 10648]
def exponent2 (i : Fin 253) : Fin 22 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 12650) : Fin 22 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 57) : List (Fin 253) :=
  (List.finRange 253).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 57 × Fin 253 :=
  (⟨selectedGenerator i % 57,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 253,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 12650) : Fin 57 × Fin 253 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*253+j)
def productIndex (i j : Fin 253) : Fin 12650 :=
  ⟨naturalProduct i.val j.val % 12650,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 12650) : List (Fin 12650) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 253) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 12650) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata22Data
