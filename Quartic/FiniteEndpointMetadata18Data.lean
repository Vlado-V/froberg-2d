import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata18Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n18/quadCodes.bin" nrows 171 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n18/quarticCodes.bin" nrows 5985 nwords 1
load_packed_tree products from "certificates/finite/n18/products.bin" nrows 29241 nwords 1
load_packed_tree coefficients from "certificates/finite/n18/coefficients.bin" nrows 40 nwords 3
load_packed_tree selectedCodes from "certificates/finite/n18/selected.bin" nrows 5985 nwords 1

def digit (code place : ℕ) : Fin 18 := ⟨code/place%18,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 171) : List (Fin 18) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 18]
def vars4 (i : Fin 5985) : List (Fin 18) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 18,
   digit (quarticCodes.get i.val) 324,digit (quarticCodes.get i.val) 5832]
def exponent2 (i : Fin 171) : Fin 18 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 5985) : Fin 18 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 40) : List (Fin 171) :=
  (List.finRange 171).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 40 × Fin 171 :=
  (⟨selectedGenerator i % 40,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 171,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 5985) : Fin 40 × Fin 171 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*171+j)
def productIndex (i j : Fin 171) : Fin 5985 :=
  ⟨naturalProduct i.val j.val % 5985,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 5985) : List (Fin 5985) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 171) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 5985) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata18Data
