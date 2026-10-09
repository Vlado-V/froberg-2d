module

public import Quartic.FiniteEndpointCheckerLoad
public import Quartic.FiniteEndpointProductRows
public import Quartic.FiniteEndpointNatural
public import Quartic.FiniteEndpointChunks

@[expose] public section

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata29Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n29/quadCodes.bin" nrows 435 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n29/quarticCodes.bin" nrows 35960 nwords 1
load_packed_tree products from "certificates/finite/n29/products.bin" nrows 189225 nwords 1
load_packed_tree coefficients from "certificates/finite/n29/coefficients.bin" nrows 93 nwords 7
load_packed_tree selectedCodes from "certificates/finite/n29/selected.bin" nrows 35960 nwords 1

def digit (code place : ℕ) : Fin 29 := ⟨code/place%29,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 435) : List (Fin 29) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 29]
def vars4 (i : Fin 35960) : List (Fin 29) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 29,
   digit (quarticCodes.get i.val) 841,digit (quarticCodes.get i.val) 24389]
def exponent2 (i : Fin 435) : Fin 29 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 35960) : Fin 29 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 93) : List (Fin 435) :=
  (List.finRange 435).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 93 × Fin 435 :=
  (⟨selectedGenerator i % 93,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 435,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 35960) : Fin 93 × Fin 435 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*435+j)
def productIndex (i j : Fin 435) : Fin 35960 :=
  ⟨naturalProduct i.val j.val % 35960,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 35960) : List (Fin 35960) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 435) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 35960) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata29Data
