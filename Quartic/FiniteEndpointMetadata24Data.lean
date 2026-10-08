import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata24Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n24/quadCodes.bin" nrows 300 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n24/quarticCodes.bin" nrows 17550 nwords 1
load_packed_tree products from "certificates/finite/n24/products.bin" nrows 90000 nwords 1
load_packed_tree coefficients from "certificates/finite/n24/coefficients.bin" nrows 66 nwords 5
load_packed_tree selectedCodes from "certificates/finite/n24/selected.bin" nrows 17550 nwords 1

def digit (code place : ℕ) : Fin 24 := ⟨code/place%24,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 300) : List (Fin 24) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 24]
def vars4 (i : Fin 17550) : List (Fin 24) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 24,
   digit (quarticCodes.get i.val) 576,digit (quarticCodes.get i.val) 13824]
def exponent2 (i : Fin 300) : Fin 24 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 17550) : Fin 24 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 66) : List (Fin 300) :=
  (List.finRange 300).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 66 × Fin 300 :=
  (⟨selectedGenerator i % 66,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 300,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 17550) : Fin 66 × Fin 300 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*300+j)
def productIndex (i j : Fin 300) : Fin 17550 :=
  ⟨naturalProduct i.val j.val % 17550,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 17550) : List (Fin 17550) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 300) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 17550) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata24Data
