import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata19Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n19/quadCodes.bin" nrows 190 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n19/quarticCodes.bin" nrows 7315 nwords 1
load_packed_tree products from "certificates/finite/n19/products.bin" nrows 36100 nwords 1
load_packed_tree coefficients from "certificates/finite/n19/coefficients.bin" nrows 44 nwords 3
load_packed_tree selectedCodes from "certificates/finite/n19/selected.bin" nrows 7315 nwords 1

def digit (code place : ℕ) : Fin 19 := ⟨code/place%19,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 190) : List (Fin 19) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 19]
def vars4 (i : Fin 7315) : List (Fin 19) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 19,
   digit (quarticCodes.get i.val) 361,digit (quarticCodes.get i.val) 6859]
def exponent2 (i : Fin 190) : Fin 19 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 7315) : Fin 19 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 44) : List (Fin 190) :=
  (List.finRange 190).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 44 × Fin 190 :=
  (⟨selectedGenerator i % 44,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 190,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 7315) : Fin 44 × Fin 190 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*190+j)
def productIndex (i j : Fin 190) : Fin 7315 :=
  ⟨naturalProduct i.val j.val % 7315,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 7315) : List (Fin 7315) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 190) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 7315) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata19Data
