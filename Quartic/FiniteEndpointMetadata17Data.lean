import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata17Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n17/quadCodes.bin" nrows 153 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n17/quarticCodes.bin" nrows 4845 nwords 1
load_packed_tree products from "certificates/finite/n17/products.bin" nrows 23409 nwords 1
load_packed_tree coefficients from "certificates/finite/n17/coefficients.bin" nrows 36 nwords 3
load_packed_tree selectedCodes from "certificates/finite/n17/selected.bin" nrows 4845 nwords 1

def digit (code place : ℕ) : Fin 17 := ⟨code/place%17,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 153) : List (Fin 17) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 17]
def vars4 (i : Fin 4845) : List (Fin 17) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 17,
   digit (quarticCodes.get i.val) 289,digit (quarticCodes.get i.val) 4913]
def exponent2 (i : Fin 153) : Fin 17 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 4845) : Fin 17 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 36) : List (Fin 153) :=
  (List.finRange 153).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 36 × Fin 153 :=
  (⟨selectedGenerator i % 36,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 153,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 4845) : Fin 36 × Fin 153 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*153+j)
def productIndex (i j : Fin 153) : Fin 4845 :=
  ⟨naturalProduct i.val j.val % 4845,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 4845) : List (Fin 4845) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 153) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 4845) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata17Data
