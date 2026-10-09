module

public import Quartic.FiniteEndpointCheckerLoad
public import Quartic.FiniteEndpointProductRows
public import Quartic.FiniteEndpointNatural
public import Quartic.FiniteEndpointChunks

@[expose] public section

/-! Compact data for the supplied thirty-variable certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata30Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n30/quadCodes.bin" nrows 465 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n30/quarticCodes.bin" nrows 40920 nwords 1
load_packed_tree products from "certificates/finite/n30/products.bin" nrows 216225 nwords 1
load_packed_tree coefficients from "certificates/finite/n30/coefficients.bin" nrows 99 nwords 8
load_packed_tree selectedCodes from "certificates/finite/n30/selected.bin" nrows 40920 nwords 1

def digit (code place : ℕ) : Fin 30 := ⟨code/place%30,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 465) : List (Fin 30) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 30]
def vars4 (i : Fin 40920) : List (Fin 30) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 30,
   digit (quarticCodes.get i.val) 900,digit (quarticCodes.get i.val) 27000]
def exponent2 (i : Fin 465) : Fin 30 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 40920) : Fin 30 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 99) : List (Fin 465) :=
  (List.finRange 465).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 99 × Fin 465 :=
  (⟨selectedGenerator i % 99,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 465,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 40920) : Fin 99 × Fin 465 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*465+j)
def productIndex (i j : Fin 465) : Fin 40920 :=
  ⟨naturalProduct i.val j.val % 40920,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 40920) : List (Fin 40920) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 465) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 40920) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata30Data
