import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Kernel-checked uniform Bernstein certificate

This file proves the 32 inequalities labelled `sc:bernstein` in
`scalar_bounds.tex`. The rational tables are generated externally, but their
connection to the stated polynomial is proved by `ring`, and every table
entry is checked nonnegative by `norm_num`. No external arithmetic result is
trusted by the proofs.
-/

namespace Quartic.UniformCertificate

noncomputable section

def knots : Fin 5 → ℝ := ![0, 1 / 3, 1 / 2, 2 / 3, 1]

def endpoint (cell : Fin 4) (side : Fin 2) : ℝ :=
  if side.val = 0 then knots cell.castSucc else knots cell.succ

def coreA (z u : ℝ) : ℝ := 2 * (z - u)
def coreB (z u : ℝ) : ℝ := z * (z - u) / 2
def freeW (z : ℝ) : ℝ := 1 - z
def quadratic (z u : ℝ) : ℝ := freeW z * (freeW z + u) / 2
def cubic (z u : ℝ) : ℝ := freeW z * (freeW z + u) * (freeW z + 2 * u) / 6
def sourceDim (z u : ℝ) : ℝ := coreA z u + 3 * freeW z
def targetDim (z u : ℝ) : ℝ :=
  coreB z u * freeW z + coreA z u * quadratic z u + 3 * cubic z u
def ell (z u x r : ℝ) : ℝ := coreA z u * x + r * freeW z
def imageBound (z u x r : ℝ) : ℝ :=
  coreB z u * freeW z * max x (r / 3) +
  coreA z u * quadratic z u * max x (min (r / 2) 1) + r * cubic z u

def denominator (cell : Fin 4) (z u x r : ℝ) : ℝ :=
  if cell = 0 then ell z u x r
  else if cell = 3 then sourceDim z u - ell z u x r
  else sourceDim z u / 2

/-- The exact left side of equation `sc:bernstein` at an endpoint of a knot
interval and an output prefix vertex. -/
def inequalityPolynomial (cell r : Fin 4) (side : Fin 2) (z u : ℝ) : ℝ :=
  100 * (sourceDim z u * imageBound z u (endpoint cell side) r.val -
    targetDim z u * ell z u (endpoint cell side) r.val) -
  sourceDim z u * denominator cell z u (endpoint cell side) r.val

/-- Tensor Bernstein basis of bidegree `(4,3)`, including binomial factors. -/
def bernstein (c : Fin 5 → Fin 4 → ℝ) (v s : ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 4,
    c i j * (Nat.choose 4 i.val : ℝ) * (Nat.choose 3 j.val : ℝ) *
      v ^ i.val * (1 - v) ^ (4 - i.val) *
      s ^ j.val * (1 - s) ^ (3 - j.val)

theorem bernstein_nonnegative (c : Fin 5 → Fin 4 → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (v s : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ bernstein c v s := by
  have hv : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hs : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have hij := hc i j
  positivity

private def coeff_0_0_0 : Fin 5 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

set_option maxHeartbeats 0 in
private theorem coeff_0_0_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_0_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_0_0]

set_option maxHeartbeats 0 in
private theorem identity_0_0_0 (v s : ℝ) :
    inequalityPolynomial 0 0 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_0_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_0_0, Fin.sum_univ_succ, Nat.choose]

private def coeff_0_0_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(155 / 24), (1637 / 256), (38887 / 6144), (1231289 / 196608)], ![(3713 / 600), (470743 / 76800), (932219 / 153600), (118111481 / 19660800)], ![(22139 / 3750), (175487 / 30000), (44497447 / 7680000), (1409917279 / 245760000)], ![(42061 / 7500), (17787 / 3200), (42295961 / 7680000), (2681141483 / 491520000)], ![(248668 / 46875), (7889201 / 1500000), (250203457 / 48000000), (7932431299 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_0_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_0_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_0_1]

set_option maxHeartbeats 0 in
private theorem identity_0_0_1 (v s : ℝ) :
    inequalityPolynomial 0 0 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_0_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_0_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_0_1_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(295 / 24), (4697 / 384), (99687 / 8192), (4759049 / 393216)], ![(14579 / 1200), (19353 / 1600), (14793637 / 1228800), (94211653 / 7864320)], ![(179641 / 15000), (5725687 / 480000), (121631081 / 10240000), (5812070863 / 491520000)], ![(88313 / 7500), (5631907 / 480000), (29922179 / 2560000), (11443332011 / 983040000)], ![(541343 / 46875), (719499 / 62500), (1101362339 / 96000000), (35113966723 / 3072000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_1_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_1_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_1_0]

set_option maxHeartbeats 0 in
private theorem identity_0_1_0 (v s : ℝ) :
    inequalityPolynomial 0 1 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_1_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_1_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_0_1_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 8), (3595 / 1152), (229627 / 73728), (1221577 / 393216)], ![(237 / 80), (170609 / 57600), (10910417 / 3686400), (116218777 / 39321600)], ![(13949 / 5000), (4021637 / 1440000), (257499293 / 92160000), (1373104271 / 491520000)], ![(1631 / 625), (1883437 / 720000), (120749593 / 46080000), (2578814059 / 983040000)], ![(37881 / 15625), (10951603 / 4500000), (703090717 / 288000000), (7517899523 / 3072000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_1_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_1_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_1_1]

set_option maxHeartbeats 0 in
private theorem identity_0_1_1 (v s : ℝ) :
    inequalityPolynomial 0 1 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_1_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_1_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_0_2_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(295 / 12), (4697 / 192), (99687 / 4096), (4759049 / 196608)], ![(14579 / 600), (19353 / 800), (14793637 / 614400), (94211653 / 3932160)], ![(179641 / 7500), (5725687 / 240000), (121631081 / 5120000), (5812070863 / 245760000)], ![(88313 / 3750), (5631907 / 240000), (29922179 / 1280000), (11443332011 / 491520000)], ![(1082686 / 46875), (719499 / 31250), (1101362339 / 48000000), (35113966723 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_2_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_2_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_2_0]

set_option maxHeartbeats 0 in
private theorem identity_0_2_0 (v s : ℝ) :
    inequalityPolynomial 0 2 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_2_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_2_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_0_2_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(185 / 12), (8843 / 576), (563405 / 36864), (996771 / 65536)], ![(9067 / 600), (867317 / 57600), (863927 / 57600), (97879507 / 6553600)], ![(27686 / 1875), (10599349 / 720000), (676089511 / 46080000), (1197529189 / 81920000)], ![(21577 / 1500), (4132519 / 288000), (131869763 / 9216000), (467404869 / 32768000)], ![(654986 / 46875), (62755531 / 4500000), (2003588867 / 144000000), (7105311041 / 512000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_2_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_2_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_2_1]

set_option maxHeartbeats 0 in
private theorem identity_0_2_1 (v s : ℝ) :
    inequalityPolynomial 0 2 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_2_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_2_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_0_3_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(85 / 4), (2029 / 96), (129127 / 6144), (42791 / 2048)], ![(4277 / 200), (408533 / 19200), (13004743 / 614400), (862267 / 40960)], ![(107291 / 5000), (2562959 / 120000), (163230401 / 7680000), (54134017 / 2560000)], ![(26837 / 1250), (10260533 / 480000), (326844181 / 15360000), (108431477 / 5120000)], ![(13387 / 625), (1279927 / 60000), (40783589 / 1920000), (13534213 / 640000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_3_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_3_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_3_0]

set_option maxHeartbeats 0 in
private theorem identity_0_3_0 (v s : ℝ) :
    inequalityPolynomial 0 3 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_3_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_3_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_0_3_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(145 / 12), (3463 / 288), (55123 / 4608), (18275 / 1536)], ![(7319 / 600), (6995 / 576), (11139491 / 921600), (3694819 / 307200)], ![(184079 / 15000), (4400021 / 360000), (140198047 / 11520000), (46521599 / 3840000)], ![(92281 / 7500), (1103297 / 90000), (281341457 / 23040000), (93393169 / 7680000)], ![(23053 / 1875), (275711 / 22500), (70330841 / 5760000), (23355097 / 1920000)]]

set_option maxHeartbeats 0 in
private theorem coeff_0_3_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_0_3_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_0_3_1]

set_option maxHeartbeats 0 in
private theorem identity_0_3_1 (v s : ℝ) :
    inequalityPolynomial 0 3 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_0_3_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_0_3_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_0_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 6), (9485 / 2304), (18733 / 4608), (262963 / 65536)], ![(949 / 240), (900629 / 230400), (222467 / 57600), (24996563 / 6553600)], ![(111791 / 30000), (663421 / 180000), (83945363 / 23040000), (294900149 / 81920000)], ![(52303 / 15000), (2484313 / 720000), (78623849 / 23040000), (552658297 / 163840000)], ![(303661 / 93750), (14429953 / 4500000), (913755517 / 288000000), (1606390033 / 512000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_0_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_0_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_0_0]

set_option maxHeartbeats 0 in
private theorem identity_1_0_0 (v s : ℝ) :
    inequalityPolynomial 1 0 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_0_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_0_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_0_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(125 / 16), (3955 / 512), (31271 / 4096), (988601 / 131072)], ![(299 / 40), (378587 / 51200), (748683 / 102400), (94718201 / 13107200)], ![(71147 / 10000), (1126527 / 160000), (35659239 / 5120000), (1128297823 / 163840000)], ![(6737 / 1000), (2134261 / 320000), (33791737 / 5120000), (2139200747 / 327680000)], ![(198343 / 31250), (1571419 / 250000), (199110657 / 32000000), (6304501699 / 1024000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_0_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_0_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_0_1]

set_option maxHeartbeats 0 in
private theorem identity_1_0_1 (v s : ℝ) :
    inequalityPolynomial 1 0 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_0_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_0_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_1_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 12), (2405 / 1152), (154103 / 73728), (274051 / 131072)], ![(29 / 15), (55913 / 28800), (7179913 / 3686400), (25587251 / 13107200)], ![(53191 / 30000), (2569843 / 1440000), (165369877 / 92160000), (295303173 / 163840000)], ![(24077 / 15000), (2332717 / 1440000), (75246869 / 46080000), (538787449 / 327680000)], ![(134261 / 93750), (407783 / 281250), (105545573 / 72000000), (1515745441 / 1024000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_1_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_1_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_1_0]

set_option maxHeartbeats 0 in
private theorem identity_1_1_0 (v s : ℝ) :
    inequalityPolynomial 1 1 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_1_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_1_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_1_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 48), (2345 / 4608), (18289 / 36864), (63251 / 131072)], ![(13 / 30), (195233 / 460800), (380797 / 921600), (5268051 / 13107200)], ![(10141 / 30000), (475993 / 1440000), (14848301 / 46080000), (51302773 / 163840000)], ![(3551 / 15000), (133231 / 576000), (10369763 / 46080000), (71432441 / 327680000)], ![(12293 / 93750), (143591 / 1125000), (35515121 / 288000000), (121058433 / 1024000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_1_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_1_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_1_1]

set_option maxHeartbeats 0 in
private theorem identity_1_1_1 (v s : ℝ) :
    inequalityPolynomial 1 1 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_1_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_1_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_2_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(125 / 8), (8965 / 576), (571339 / 36864), (3033289 / 196608)], ![(1223 / 80), (877651 / 57600), (6995711 / 460800), (297303289 / 19660800)], ![(149097 / 10000), (10705559 / 720000), (683054051 / 46080000), (3630609647 / 245760000)], ![(14497 / 1000), (4165961 / 288000), (132974287 / 9216000), (1414357583 / 98304000)], ![(439199 / 31250), (63139031 / 4500000), (4032826109 / 288000000), (21458531123 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_2_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_2_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_2_0]

set_option maxHeartbeats 0 in
private theorem identity_1_2_0 (v s : ℝ) :
    inequalityPolynomial 1 2 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_2_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_2_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_2_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(275 / 24), (4385 / 384), (11649 / 1024), (2227289 / 196608)], ![(2669 / 240), (106471 / 9600), (13586171 / 1228800), (216625289 / 19660800)], ![(322591 / 30000), (5151031 / 480000), (27406057 / 2560000), (2623655647 / 245760000)], ![(31081 / 3000), (993257 / 96000), (21152741 / 2048000), (1013182783 / 98304000)], ![(932597 / 93750), (465986 / 46875), (29791229 / 3000000), (15230881123 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_2_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_2_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_2_1]

set_option maxHeartbeats 0 in
private theorem identity_1_2_1 (v s : ℝ) :
    inequalityPolynomial 1 2 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_2_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_2_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_3_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(325 / 24), (7765 / 576), (247307 / 18432), (82027 / 6144)], ![(3259 / 240), (778951 / 57600), (12409297 / 921600), (4117601 / 307200)], ![(407291 / 30000), (9738359 / 720000), (77598247 / 5760000), (25757999 / 1920000)], ![(202999 / 15000), (19421329 / 1440000), (309615439 / 23040000), (102809663 / 7680000)], ![(50437 / 3750), (2413451 / 180000), (153949889 / 11520000), (51136513 / 3840000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_3_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_3_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_3_0]

set_option maxHeartbeats 0 in
private theorem identity_1_3_0 (v s : ℝ) :
    inequalityPolynomial 1 3 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_3_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_3_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_1_3_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(75 / 8), (1195 / 128), (38071 / 4096), (37893 / 4096)], ![(753 / 80), (30007 / 3200), (3825557 / 409600), (3809343 / 409600)], ![(94197 / 10000), (1502077 / 160000), (47893439 / 5120000), (47709789 / 5120000)], ![(46983 / 5000), (1498931 / 160000), (95621359 / 10240000), (95290509 / 10240000)], ![(11679 / 1250), (46591 / 5000), (2973199 / 320000), (2963949 / 320000)]]

set_option maxHeartbeats 0 in
private theorem coeff_1_3_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_1_3_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_1_3_1]

set_option maxHeartbeats 0 in
private theorem identity_1_3_1 (v s : ℝ) :
    inequalityPolynomial 1 3 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_1_3_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_1_3_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_0_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(125 / 16), (3955 / 512), (31271 / 4096), (988601 / 131072)], ![(299 / 40), (378587 / 51200), (748683 / 102400), (94718201 / 13107200)], ![(71147 / 10000), (1126527 / 160000), (35659239 / 5120000), (1128297823 / 163840000)], ![(6737 / 1000), (2134261 / 320000), (33791737 / 5120000), (2139200747 / 327680000)], ![(198343 / 31250), (1571419 / 250000), (199110657 / 32000000), (6304501699 / 1024000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_0_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_0_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_0_0]

set_option maxHeartbeats 0 in
private theorem identity_2_0_0 (v s : ℝ) :
    inequalityPolynomial 2 0 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_0_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_0_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_0_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(275 / 24), (13055 / 1152), (206507 / 18432), (362819 / 32768)], ![(2639 / 240), (1253327 / 115200), (4958411 / 460800), (34860819 / 3276800)], ![(315091 / 30000), (7485059 / 720000), (59246947 / 5760000), (416698837 / 40960000)], ![(149807 / 15000), (14239723 / 1440000), (28187723 / 2880000), (31730849 / 3276800)], ![(886397 / 93750), (42141131 / 4500000), (2670236309 / 288000000), (2349055833 / 256000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_0_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_0_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_0_1]

set_option maxHeartbeats 0 in
private theorem identity_2_0_1 (v s : ℝ) :
    inequalityPolynomial 2 0 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_0_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_0_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_1_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 48), (2345 / 4608), (18289 / 36864), (63251 / 131072)], ![(13 / 30), (195233 / 460800), (380797 / 921600), (5268051 / 13107200)], ![(10141 / 30000), (475993 / 1440000), (14848301 / 46080000), (51302773 / 163840000)], ![(3551 / 15000), (133231 / 576000), (10369763 / 46080000), (71432441 / 327680000)], ![(12293 / 93750), (143591 / 1125000), (35515121 / 288000000), (121058433 / 1024000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_1_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_1_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_1_0]

set_option maxHeartbeats 0 in
private theorem identity_2_1_0 (v s : ℝ) :
    inequalityPolynomial 2 1 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_1_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_1_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_1_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 6), (9485 / 2304), (18733 / 4608), (262963 / 65536)], ![(949 / 240), (900629 / 230400), (222467 / 57600), (24996563 / 6553600)], ![(111791 / 30000), (663421 / 180000), (83945363 / 23040000), (294900149 / 81920000)], ![(52303 / 15000), (2484313 / 720000), (78623849 / 23040000), (552658297 / 163840000)], ![(303661 / 93750), (14429953 / 4500000), (913755517 / 288000000), (1606390033 / 512000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_1_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_1_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_1_1]

set_option maxHeartbeats 0 in
private theorem identity_2_1_1 (v s : ℝ) :
    inequalityPolynomial 2 1 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_1_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_1_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_2_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(275 / 24), (4385 / 384), (11649 / 1024), (2227289 / 196608)], ![(2669 / 240), (106471 / 9600), (13586171 / 1228800), (216625289 / 19660800)], ![(322591 / 30000), (5151031 / 480000), (27406057 / 2560000), (2623655647 / 245760000)], ![(31081 / 3000), (993257 / 96000), (21152741 / 2048000), (1013182783 / 98304000)], ![(932597 / 93750), (465986 / 46875), (29791229 / 3000000), (15230881123 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_2_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_2_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_2_0]

set_option maxHeartbeats 0 in
private theorem identity_2_2_0 (v s : ℝ) :
    inequalityPolynomial 2 2 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_2_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_2_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_2_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(175 / 24), (2095 / 288), (267389 / 36864), (473763 / 65536)], ![(1669 / 240), (400001 / 57600), (12775669 / 1843200), (45315763 / 6553600)], ![(197891 / 30000), (2373767 / 360000), (303564001 / 46080000), (538900549 / 81920000)], ![(18671 / 3000), (1793581 / 288000), (28700191 / 4608000), (204002661 / 32768000)], ![(547597 / 93750), (26330281 / 4500000), (1687089859 / 288000000), (3001077041 / 512000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_2_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_2_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_2_1]

set_option maxHeartbeats 0 in
private theorem identity_2_2_1 (v s : ℝ) :
    inequalityPolynomial 2 2 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_2_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_2_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_3_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(75 / 8), (1195 / 128), (38071 / 4096), (37893 / 4096)], ![(753 / 80), (30007 / 3200), (3825557 / 409600), (3809343 / 409600)], ![(94197 / 10000), (1502077 / 160000), (47893439 / 5120000), (47709789 / 5120000)], ![(46983 / 5000), (1498931 / 160000), (95621359 / 10240000), (95290509 / 10240000)], ![(11679 / 1250), (46591 / 5000), (2973199 / 320000), (2963949 / 320000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_3_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_3_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_3_0]

set_option maxHeartbeats 0 in
private theorem identity_2_3_0 (v s : ℝ) :
    inequalityPolynomial 2 3 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_3_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_3_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_2_3_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(125 / 24), (1495 / 288), (23833 / 4608), (7913 / 1536)], ![(1259 / 240), (301301 / 57600), (9611419 / 1843200), (3192827 / 614400)], ![(157891 / 30000), (1890167 / 360000), (120647963 / 23040000), (40097371 / 7680000)], ![(78899 / 15000), (7559429 / 1440000), (241361353 / 46080000), (80252201 / 15360000)], ![(19637 / 3750), (941101 / 180000), (60120439 / 11520000), (19998263 / 3840000)]]

set_option maxHeartbeats 0 in
private theorem coeff_2_3_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_2_3_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_2_3_1]

set_option maxHeartbeats 0 in
private theorem identity_2_3_1 (v s : ℝ) :
    inequalityPolynomial 2 3 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_2_3_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_2_3_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_0_0 : Fin 5 → Fin 4 → ℝ :=
  ![![10, (11377 / 1152), (44923 / 4608), (945625 / 98304)], ![(1923 / 200), (43777 / 4608), (1080877 / 115200), (91053433 / 9830400)], ![(45993 / 5000), (3273371 / 360000), (103495447 / 11520000), (1090275743 / 122880000)], ![(4379 / 500), (6235573 / 720000), (98613901 / 11520000), (2078485867 / 245760000)], ![(129687 / 15625), (2309191 / 281250), (1169015567 / 144000000), (6161903699 / 768000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_0_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_0_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_0_0]

set_option maxHeartbeats 0 in
private theorem identity_3_0_0 (v s : ℝ) :
    inequalityPolynomial 3 0 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_0_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_0_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_0_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(145 / 8), (13757 / 768), (108727 / 6144), (1145337 / 65536)], ![(1751 / 100), (1329557 / 76800), (2628067 / 153600), (22156389 / 1310720)], ![(84241 / 5000), (999817 / 60000), (126527801 / 7680000), (1333873119 / 81920000)], ![(10094 / 625), (766973 / 48000), (121365263 / 7680000), (2559711723 / 163840000)], ![(241043 / 15625), (22900603 / 1500000), (181240499 / 12000000), (7647235299 / 512000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_0_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_0_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_0_1]

set_option maxHeartbeats 0 in
private theorem identity_3_0_1 (v s : ℝ) :
    inequalityPolynomial 3 0 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_0_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_0_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_1_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(95 / 24), (2999 / 768), (7885 / 2048), (745913 / 196608)], ![(2267 / 600), (95477 / 25600), (565147 / 153600), (71324921 / 19660800)], ![(26869 / 7500), (424579 / 120000), (26821031 / 7680000), (846678367 / 245760000)], ![(25309 / 7500), (200059 / 60000), (8429171 / 2560000), (1597260011 / 491520000)], ![(148018 / 46875), (1560717 / 500000), (148017857 / 48000000), (4676572099 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_1_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_1_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_1_0]

set_option maxHeartbeats 0 in
private theorem identity_3_1_0 (v s : ℝ) :
    inequalityPolynomial 3 1 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_1_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_1_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_1_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(145 / 12), (13757 / 1152), (108727 / 9216), (381779 / 32768)], ![(1751 / 150), (1329557 / 115200), (2628067 / 230400), (7385463 / 655360)], ![(84241 / 7500), (999817 / 90000), (126527801 / 11520000), (444624373 / 40960000)], ![(20188 / 1875), (766973 / 72000), (121365263 / 11520000), (853237241 / 81920000)], ![(482086 / 46875), (22900603 / 2250000), (181240499 / 18000000), (2549078433 / 256000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_1_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_1_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_1_1]

set_option maxHeartbeats 0 in
private theorem identity_3_1_1 (v s : ℝ) :
    inequalityPolynomial 3 1 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_1_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_1_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_2_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(25 / 3), (1595 / 192), (101717 / 12288), (1621001 / 196608)], ![(479 / 60), (1593 / 200), (1626769 / 204800), (155675801 / 19660800)], ![(114197 / 15000), (608159 / 80000), (116542903 / 15360000), (1860299023 / 245760000)], ![(54211 / 7500), (1733677 / 240000), (55417439 / 7680000), (3541265771 / 491520000)], ![(320311 / 46875), (854371 / 125000), (54666619 / 8000000), (10488562723 / 1536000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_2_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_2_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_2_0]

set_option maxHeartbeats 0 in
private theorem identity_3_2_0 (v s : ℝ) :
    inequalityPolynomial 3 2 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_2_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_2_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_2_1 : Fin 5 → Fin 4 → ℝ :=
  ![![(145 / 24), (13757 / 2304), (108727 / 18432), (381779 / 65536)], ![(1751 / 300), (1329557 / 230400), (2628067 / 460800), (7385463 / 1310720)], ![(84241 / 15000), (999817 / 180000), (126527801 / 23040000), (444624373 / 81920000)], ![(10094 / 1875), (766973 / 144000), (121365263 / 23040000), (853237241 / 163840000)], ![(241043 / 46875), (22900603 / 4500000), (181240499 / 36000000), (2549078433 / 512000000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_2_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_2_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_2_1]

set_option maxHeartbeats 0 in
private theorem identity_3_2_1 (v s : ℝ) :
    inequalityPolynomial 3 2 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_2_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_2_1, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_3_0 : Fin 5 → Fin 4 → ℝ :=
  ![![(15 / 2), (239 / 32), (15229 / 2048), (15159 / 2048)], ![(187 / 25), (47689 / 6400), (4559701 / 614400), (1513461 / 204800)], ![(18601 / 2500), (889723 / 120000), (18910549 / 2560000), (18836799 / 2560000)], ![(18453 / 2500), (1177217 / 160000), (37543269 / 5120000), (37408719 / 5120000)], ![(4564 / 625), (145623 / 20000), (3484127 / 480000), (1157559 / 160000)]]

set_option maxHeartbeats 0 in
private theorem coeff_3_3_0_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_3_0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_3_0]

set_option maxHeartbeats 0 in
private theorem identity_3_3_0 (v s : ℝ) :
    inequalityPolynomial 3 3 0 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_3_0 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_3_0, Fin.sum_univ_succ, Nat.choose]
  ring

private def coeff_3_3_1 : Fin 5 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

set_option maxHeartbeats 0 in
private theorem coeff_3_3_1_nonnegative (i : Fin 5) (j : Fin 4) :
    0 ≤ coeff_3_3_1 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coeff_3_3_1]

set_option maxHeartbeats 0 in
private theorem identity_3_3_1 (v s : ℝ) :
    inequalityPolynomial 3 3 1 (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein coeff_3_3_1 v s := by
  norm_num [inequalityPolynomial, sourceDim, targetDim, imageBound,
    denominator, ell, coreA, coreB, freeW, quadratic, cubic,
    endpoint, knots, bernstein, coeff_3_3_1, Fin.sum_univ_succ, Nat.choose]
  ring

/-- Explicit rational Bernstein coefficients for all 32 actual polynomials.
Lower-degree cases have been degree-elevated to the same tensor basis. -/
def coefficients : Fin 4 → Fin 4 → Fin 2 → Fin 5 → Fin 4 → ℝ :=
  ![![![coeff_0_0_0, coeff_0_0_1], ![coeff_0_1_0, coeff_0_1_1], ![coeff_0_2_0, coeff_0_2_1], ![coeff_0_3_0, coeff_0_3_1]], ![![coeff_1_0_0, coeff_1_0_1], ![coeff_1_1_0, coeff_1_1_1], ![coeff_1_2_0, coeff_1_2_1], ![coeff_1_3_0, coeff_1_3_1]], ![![coeff_2_0_0, coeff_2_0_1], ![coeff_2_1_0, coeff_2_1_1], ![coeff_2_2_0, coeff_2_2_1], ![coeff_2_3_0, coeff_2_3_1]], ![![coeff_3_0_0, coeff_3_0_1], ![coeff_3_1_0, coeff_3_1_1], ![coeff_3_2_0, coeff_3_2_1], ![coeff_3_3_0, coeff_3_3_1]]]

theorem coefficients_nonnegative (cell r : Fin 4) (side : Fin 2)
    (i : Fin 5) (j : Fin 4) : 0 ≤ coefficients cell r side i j := by
  fin_cases cell <;> fin_cases r <;> fin_cases side
  · exact coeff_0_0_0_nonnegative i j
  · exact coeff_0_0_1_nonnegative i j
  · exact coeff_0_1_0_nonnegative i j
  · exact coeff_0_1_1_nonnegative i j
  · exact coeff_0_2_0_nonnegative i j
  · exact coeff_0_2_1_nonnegative i j
  · exact coeff_0_3_0_nonnegative i j
  · exact coeff_0_3_1_nonnegative i j
  · exact coeff_1_0_0_nonnegative i j
  · exact coeff_1_0_1_nonnegative i j
  · exact coeff_1_1_0_nonnegative i j
  · exact coeff_1_1_1_nonnegative i j
  · exact coeff_1_2_0_nonnegative i j
  · exact coeff_1_2_1_nonnegative i j
  · exact coeff_1_3_0_nonnegative i j
  · exact coeff_1_3_1_nonnegative i j
  · exact coeff_2_0_0_nonnegative i j
  · exact coeff_2_0_1_nonnegative i j
  · exact coeff_2_1_0_nonnegative i j
  · exact coeff_2_1_1_nonnegative i j
  · exact coeff_2_2_0_nonnegative i j
  · exact coeff_2_2_1_nonnegative i j
  · exact coeff_2_3_0_nonnegative i j
  · exact coeff_2_3_1_nonnegative i j
  · exact coeff_3_0_0_nonnegative i j
  · exact coeff_3_0_1_nonnegative i j
  · exact coeff_3_1_0_nonnegative i j
  · exact coeff_3_1_1_nonnegative i j
  · exact coeff_3_2_0_nonnegative i j
  · exact coeff_3_2_1_nonnegative i j
  · exact coeff_3_3_0_nonnegative i j
  · exact coeff_3_3_1_nonnegative i j

theorem normalized_identity (cell r : Fin 4) (side : Fin 2) (v s : ℝ) :
    inequalityPolynomial cell r side (1 / 2 + (3 / 50) * v) (s / 64) =
      bernstein (coefficients cell r side) v s := by
  fin_cases cell <;> fin_cases r <;> fin_cases side
  · exact identity_0_0_0 v s
  · exact identity_0_0_1 v s
  · exact identity_0_1_0 v s
  · exact identity_0_1_1 v s
  · exact identity_0_2_0 v s
  · exact identity_0_2_1 v s
  · exact identity_0_3_0 v s
  · exact identity_0_3_1 v s
  · exact identity_1_0_0 v s
  · exact identity_1_0_1 v s
  · exact identity_1_1_0 v s
  · exact identity_1_1_1 v s
  · exact identity_1_2_0 v s
  · exact identity_1_2_1 v s
  · exact identity_1_3_0 v s
  · exact identity_1_3_1 v s
  · exact identity_2_0_0 v s
  · exact identity_2_0_1 v s
  · exact identity_2_1_0 v s
  · exact identity_2_1_1 v s
  · exact identity_2_2_0 v s
  · exact identity_2_2_1 v s
  · exact identity_2_3_0 v s
  · exact identity_2_3_1 v s
  · exact identity_3_0_0 v s
  · exact identity_3_0_1 v s
  · exact identity_3_1_0 v s
  · exact identity_3_1_1 v s
  · exact identity_3_2_0 v s
  · exact identity_3_2_1 v s
  · exact identity_3_3_0 v s
  · exact identity_3_3_1 v s

theorem normalized_nonnegative (cell r : Fin 4) (side : Fin 2) (v s : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ inequalityPolynomial cell r side (1 / 2 + (3 / 50) * v) (s / 64) := by
  rw [normalized_identity]
  exact bernstein_nonnegative _ (coefficients_nonnegative cell r side) v s hv0 hv1 hs0 hs1

/-- All 32 rational polynomial inequalities from `sc:bernstein`, on the full
closed rectangle stated in the manuscript. -/
theorem uniform_bernstein_inequality (cell r : Fin 4) (side : Fin 2) (z u : ℝ)
    (hz0 : 1 / 2 ≤ z) (hz1 : z ≤ 14 / 25)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 64) :
    0 ≤ inequalityPolynomial cell r side z u := by
  let v : ℝ := (z - 1 / 2) * (50 / 3)
  let s : ℝ := 64 * u
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hv1 : v ≤ 1 := by dsimp [v]; linarith
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hz : (1 / 2 : ℝ) + (3 / 50) * v = z := by dsimp [v]; ring
  have hu : s / 64 = u := by dsimp [s]; ring
  simpa only [hz, hu] using normalized_nonnegative cell r side v s hv0 hv1 hs0 hs1

end

end Quartic.UniformCertificate
