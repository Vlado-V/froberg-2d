import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata21Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n21/quadCodes.bin" nrows 231 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n21/quarticCodes.bin" nrows 10626 nwords 1
load_packed_tree products from "certificates/finite/n21/products.bin" nrows 53361 nwords 1
load_packed_tree coefficients from "certificates/finite/n21/coefficients.bin" nrows 52 nwords 4
load_packed_tree selectedCodes from "certificates/finite/n21/selected.bin" nrows 10626 nwords 1

def digit (code place : ℕ) : Fin 21 := ⟨code/place%21,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 231) : List (Fin 21) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 21]
def vars4 (i : Fin 10626) : List (Fin 21) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 21,
   digit (quarticCodes.get i.val) 441,digit (quarticCodes.get i.val) 9261]
def exponent2 (i : Fin 231) : Fin 21 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 10626) : Fin 21 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 52) : List (Fin 231) :=
  (List.finRange 231).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 52 × Fin 231 :=
  (⟨selectedGenerator i % 52,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 231,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 10626) : Fin 52 × Fin 231 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*231+j)
def productIndex (i j : Fin 231) : Fin 10626 :=
  ⟨naturalProduct i.val j.val % 10626,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 10626) : List (Fin 10626) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 231) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 10626) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata21Data
