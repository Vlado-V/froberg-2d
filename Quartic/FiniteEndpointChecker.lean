module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic

@[expose] public section

/-!
A kernel-checkable packed binary inverse certificate primitive. This module
does not claim that any manuscript endpoint has supplied such an inverse.
-/
namespace Quartic.FiniteEndpointChecker
open Matrix Module
set_option maxHeartbeats 1000000

/-- Decode a packed natural number as a binary row of a specified width. -/
def unpack (n : ℕ) (x : ℕ) : Fin n → ZMod 2 :=
  fun i => if x.testBit i.val then 1 else 0

theorem unpack_xor (n x y : ℕ) : unpack n (x ^^^ y) = unpack n x + unpack n y := by
  funext i
  cases hx : x.testBit i.val <;> cases hy : y.testBit i.val <;>
    norm_num [unpack,Nat.testBit_xor,hx,hy] <;> decide

@[simp] theorem unpack_zero (n : ℕ) : unpack n 0 = 0 := by
  funext i
  simp [unpack]

@[simp] theorem unpack_unit {n : ℕ} (i : Fin n) : unpack n (2^i.val) = Pi.single i 1 := by
  classical
  funext j
  simp only [unpack,Nat.testBit_two_pow,Pi.single_apply]
  simp [Fin.ext_iff,eq_comm]

/-- XOR a sparse list of packed rows; repetitions cancel over F₂. -/
def xorSum : List ℕ → ℕ
  | [] => 0
  | x::xs => x ^^^ xorSum xs

theorem unpack_xorSum (n : ℕ) (xs : List ℕ) :
    unpack n (xorSum xs) = (xs.map (unpack n)).sum := by
  induction xs with
  | nil => simp [xorSum]
  | cons x xs ih => simp only [xorSum,unpack_xor,ih,List.map_cons,List.sum_cons]

/-- A sparse row is a sum of coordinate basis vectors. -/
def sparseRow {n : ℕ} (s : List (Fin n)) : Fin n → ZMod 2 :=
  (s.map (fun i => Pi.single i (1 : ZMod 2))).sum

def sparseMatrix {r n : ℕ} (A : Fin r → List (Fin n)) : Matrix (Fin r) (Fin n) (ZMod 2) :=
  fun i => sparseRow (A i)

theorem sparseRow_vecMul {n k : ℕ} (s : List (Fin n)) (B : Matrix (Fin n) (Fin k) (ZMod 2)) :
    sparseRow s ᵥ* B = (s.map (fun i => B i)).sum := by
  induction s with
  | nil => simp [sparseRow]
  | cons i s ih =>
    simp only [sparseRow,List.map_cons,List.sum_cons,add_vecMul,single_one_vecMul]
    exact congrArg (fun v => B i + v) ih

/-- Exactly the sparse inverse equations; no determinant is computed. -/
def checkInverse {n : ℕ} (A : Fin n → List (Fin n)) (B : Fin n → ℕ) : Bool :=
  (List.finRange n).all (fun i => decide (xorSum ((A i).map B) = 2^i.val))

theorem checkInverse_equations {n : ℕ} (A : Fin n → List (Fin n)) (B : Fin n → ℕ)
    (h : checkInverse A B = true) : ∀ i, xorSum ((A i).map B) = 2^i.val := by
  intro i
  have hi := List.all_eq_true.mp h i (by simp)
  exact of_decide_eq_true hi

def packedMatrix (n : ℕ) (B : Fin n → ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of (fun i => unpack n (B i))

/-- The verified packed-row equations give a literal matrix right inverse. -/
theorem inverse_identity {n : ℕ} (A : Fin n → List (Fin n)) (B : Fin n → ℕ)
    (h : checkInverse A B = true) :
    sparseMatrix A * packedMatrix n B = 1 := by
  ext i j
  have he := congrFun (congrArg (unpack n) (checkInverse_equations A B h i)) j
  rw [unpack_xorSum,unpack_unit] at he
  have hrow := sparseRow_vecMul (A i) (packedMatrix n B)
  change (sparseRow (A i) ᵥ* packedMatrix n B) j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j
  rw [hrow]
  change ((A i).map (fun k => unpack n (B k))).sum j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j
  simpa only [List.map_map,Function.comp_def,Pi.single_apply,Matrix.one_apply,eq_comm] using he

/-- Kernel verification of a sparse inverse certificate proves the determinant nonzero. -/
theorem determinant_ne_zero {n : ℕ} (A : Fin n → List (Fin n)) (B : Fin n → ℕ)
    (h : checkInverse A B = true) : (sparseMatrix A).det ≠ 0 := by
  have hd := congrArg Matrix.det (inverse_identity A B h)
  rw [Matrix.det_mul,Matrix.det_one] at hd
  intro hz
  rw [hz,zero_mul] at hd
  exact zero_ne_one hd

/-- The same checked certificate proves full binary rank. -/
theorem full_rank {n : ℕ} (A : Fin n → List (Fin n)) (B : Fin n → ℕ)
    (h : checkInverse A B = true) : (sparseMatrix A).rank = n := by
  simpa using Matrix.rank_of_det_ne_zero (determinant_ne_zero A B h)

/-- A small nontrivial certificate exercises the actual Boolean checker. -/
def testRows : Fin 3 → List (Fin 3) := ![[0,1],[1,2],[0,1,2]]
def testInverse : Fin 3 → ℕ := ![6,7,5]

theorem test_inverse_checked : checkInverse testRows testInverse = true := by decide

theorem test_full_rank : (sparseMatrix testRows).rank = 3 :=
  full_rank testRows testInverse test_inverse_checked

end Quartic.FiniteEndpointChecker
