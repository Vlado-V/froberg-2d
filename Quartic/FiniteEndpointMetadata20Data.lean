import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata20Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n20/quadCodes.bin" nrows 210 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n20/quarticCodes.bin" nrows 8855 nwords 1
load_packed_tree products from "certificates/finite/n20/products.bin" nrows 44100 nwords 1
load_packed_tree coefficients from "certificates/finite/n20/coefficients.bin" nrows 48 nwords 4
load_packed_tree selectedCodes from "certificates/finite/n20/selected.bin" nrows 8855 nwords 1

def digit (code place : ℕ) : Fin 20 := ⟨code/place%20,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 210) : List (Fin 20) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 20]
def vars4 (i : Fin 8855) : List (Fin 20) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 20,
   digit (quarticCodes.get i.val) 400,digit (quarticCodes.get i.val) 8000]
def exponent2 (i : Fin 210) : Fin 20 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 8855) : Fin 20 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 48) : List (Fin 210) :=
  (List.finRange 210).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 48 × Fin 210 :=
  (⟨selectedGenerator i % 48,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 210,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 8855) : Fin 48 × Fin 210 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*210+j)
def productIndex (i j : Fin 210) : Fin 8855 :=
  ⟨naturalProduct i.val j.val % 8855,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 8855) : List (Fin 8855) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 210) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 8855) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata20Data
