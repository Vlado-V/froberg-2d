import Quartic.FiniteEndpointCheckerLoad
import Quartic.FiniteEndpointProductRows
import Quartic.FiniteEndpointNatural
import Quartic.FiniteEndpointChunks

/-! Compact data for a supplied finite certificate. These declarations
contain data only; all required properties are proved in separate modules. -/
noncomputable section
namespace Quartic.FiniteEndpointMetadata27Data
open FiniteEndpointCheckerPolynomial
set_option maxRecDepth 1000000
set_option Elab.async false

load_packed_tree quadCodes from "certificates/finite/n27/quadCodes.bin" nrows 378 nwords 1
load_packed_tree quarticCodes from "certificates/finite/n27/quarticCodes.bin" nrows 27405 nwords 1
load_packed_tree products from "certificates/finite/n27/products.bin" nrows 142884 nwords 1
load_packed_tree coefficients from "certificates/finite/n27/coefficients.bin" nrows 82 nwords 6
load_packed_tree selectedCodes from "certificates/finite/n27/selected.bin" nrows 27405 nwords 1

def digit (code place : ℕ) : Fin 27 := ⟨code/place%27,Nat.mod_lt _ (by decide)⟩
def vars2 (i : Fin 378) : List (Fin 27) :=
  [digit (quadCodes.get i.val) 1,digit (quadCodes.get i.val) 27]
def vars4 (i : Fin 27405) : List (Fin 27) :=
  [digit (quarticCodes.get i.val) 1,digit (quarticCodes.get i.val) 27,
   digit (quarticCodes.get i.val) 729,digit (quarticCodes.get i.val) 19683]
def exponent2 (i : Fin 378) : Fin 27 →₀ ℕ := listExponent (vars2 i)
def exponent4 (i : Fin 27405) : Fin 27 →₀ ℕ := listExponent (vars4 i)

def quadSupport (g : Fin 82) : List (Fin 378) :=
  (List.finRange 378).filter (fun j => (coefficients.get g.val).testBit j.val)
def selectedGenerator (i : ℕ) : ℕ := selectedCodes.get i % 4294967296
 def selectedMultiplier (i : ℕ) : ℕ := selectedCodes.get i / 4294967296
def selectedRaw (i : ℕ) : Fin 82 × Fin 378 :=
  (⟨selectedGenerator i % 82,Nat.mod_lt _ (by decide)⟩,
   ⟨selectedMultiplier i % 378,Nat.mod_lt _ (by decide)⟩)
def selected (i : Fin 27405) : Fin 82 × Fin 378 := selectedRaw i.val

def naturalProduct (i j : ℕ) : ℕ := products.get (i*378+j)
def productIndex (i j : Fin 378) : Fin 27405 :=
  ⟨naturalProduct i.val j.val % 27405,Nat.mod_lt _ (by decide)⟩
def naturalRow (i : ℕ) : List ℕ :=
  (quadSupport (selectedRaw i).1).map (fun j => naturalProduct j.val (selectedRaw i).2.val)
def rows (i : Fin 27405) : List (Fin 27405) :=
  FiniteEndpointProductRows.rows productIndex quadSupport selected i

theorem rows_eq_natural : rows = FiniteEndpointNatural.finRows (by decide) naturalRow := by
  funext i
  simp only [rows,FiniteEndpointProductRows.rows,FiniteEndpointNatural.finRows,
    naturalRow,selected,productIndex,List.map_map,Function.comp_def]

theorem exponent2_degree (i : Fin 378) : (exponent2 i).degree = 2 := by
  rw [exponent2,listExponent_degree]
  rfl

theorem exponent4_degree (i : Fin 27405) : (exponent4 i).degree = 4 := by
  rw [exponent4,listExponent_degree]
  rfl

end Quartic.FiniteEndpointMetadata27Data
