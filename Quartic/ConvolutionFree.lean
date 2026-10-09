module

public import Quartic.FreeCoefficients
public import Quartic.ConvolutionHilbert

@[expose] public section

/-!
# Adjoining arbitrarily many free variables to the actual convolution module

The presentation uses its original `t` core variables in a polynomial ring
on `t+w` variables. Taking every free-monomial coefficient reduces a putative
low-degree syzygy to the proved core injectivity theorem. Consequently no
new coefficient syzygies appear in degrees zero, one, or two, for any `w`.
-/

noncomputable section
namespace Quartic.ConvolutionFree
open MvPolynomial ConvolutionPresentation ConvolutionHilbert FreeCoefficients
variable {K : Type*} [Field K] {t w j : ℕ}

abbrev Source (K : Type*) [Field K] (t w j : ℕ) :=
  Fin (t + 2) → Quartic.Forms K (t + w) j
abbrev Target (K : Type*) [Field K] (t w j : ℕ) :=
  Fin 3 → Quartic.Forms K (t + w) j

/-- The original columns, now in the polynomial ring with free variables. -/
def presentation : Source K t w j →ₗ[K] Target K t w (j + 1) :=
  LinearMap.pi fun d => ∑ i : Fin t,
    (variableMul (Fin.castAdd w i)).comp (LinearMap.proj (columnIndex d i))

@[simp] theorem presentation_apply_val (a : Source K t w j) (d : Fin 3) :
    (presentation a d).val = ∑ i : Fin t, X (Fin.castAdd w i) * (a (columnIndex d i)).val := by
  simp [presentation, variableMul]

/-- Positive-degree graded pieces of the actual extended cokernel. -/
abbrev Cokernel (K : Type*) [Field K] (t w j : ℕ) :=
  Target K t w (j + 1) ⧸ LinearMap.range (presentation (K := K) (t := t) (w := w) (j := j))

/-- Extract a free monomial from every source column. -/
def sourceCoeff (b : Fin w →₀ ℕ) :
    Source K t w j →ₗ[K] ConvolutionPresentation.Source K t (j - b.degree) :=
  LinearMap.pi fun k => (homogeneousCoeff b).comp (LinearMap.proj k)

@[simp] theorem sourceCoeff_apply_val (b : Fin w →₀ ℕ) (a : Source K t w j)
    (k : Fin (t + 2)) : (sourceCoeff b a k).val = freeCoeff b (a k).val := rfl

/-- Every free coefficient of an extended relation is a relation of the core presentation. -/
theorem sourceCoeff_kernel (b : Fin w →₀ ℕ) (a : Source K t w j)
    (ha : presentation a = 0) :
    ConvolutionPresentation.presentation (sourceCoeff b a) = 0 := by
  funext d
  apply Subtype.ext
  have hd := congrArg (fun v : Target K t w (j + 1) => (v d).val) ha
  have hc := congrArg (freeCoeff b) hd
  simp only [presentation_apply_val, map_sum, freeCoeff_core_X_mul, Pi.zero_apply,
    ZeroMemClass.coe_zero, map_zero] at hc
  simpa only [ConvolutionPresentation.presentation_apply_val, sourceCoeff_apply_val,
    Pi.zero_apply, ZeroMemClass.coe_zero] using hc

/-- Polynomial extension creates no coefficient syzygies in the first three degrees. -/
theorem presentation_injective (ht : 2 ≤ t) (hj : j ≤ 2) :
    Function.Injective (presentation (K := K) (t := t) (w := w) (j := j)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a ha
  change a = 0
  have hz : presentation a = 0 := ha
  funext k
  apply Subtype.ext
  apply eq_zero_of_freeCoeff
  intro b
  have hcore : Function.Injective
      (ConvolutionPresentation.presentation (K := K) (t := t) (j := j - b.degree)) :=
    no_coefficient_syzygies ht ⟨j - b.degree, by omega⟩
  have hb : sourceCoeff b a = 0 := hcore ((sourceCoeff_kernel b a hz).trans (map_zero _).symm)
  exact congrArg (fun v : ConvolutionPresentation.Source K t (j - b.degree) => (v k).val) hb

/-- The extended Hilbert dimensions follow from the actual injective presentation. -/
theorem cokernel_euler (ht : 2 ≤ t) (hj : j ≤ 2) :
    Module.finrank K (Cokernel K t w j) +
      (t + 2) * (t + w + j - 1).choose j =
        3 * (t + w + j).choose (j + 1) := by
  have h := (LinearMap.range
    (presentation (K := K) (t := t) (w := w) (j := j))).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj (presentation_injective ht hj)] at h
  have hs : Module.finrank K (Source K t w j) =
      (t + 2) * (t + w + j - 1).choose j := by
    simp [Source, Module.finrank_pi_fintype, Quartic.finrank_forms]
  have hd : Module.finrank K (Target K t w (j + 1)) =
      3 * (t + w + j).choose (j + 1) := by
    simp [Target, Module.finrank_pi_fintype, Quartic.finrank_forms, Nat.add_assoc]
    congr 1
  change Module.finrank K (Cokernel K t w j) + Module.finrank K (Source K t w j) =
    Module.finrank K (Target K t w (j + 1)) at h
  rwa [hs, hd] at h

/-- The first piece is the core first piece plus three copies of the free variables. -/
theorem degreeOne_finrank (ht : 2 ≤ t) :
    Module.finrank K (Cokernel K t w 0) = 2 * (t - 1) + 3 * w := by
  have h := cokernel_euler (K := K) (w := w) ht (j := 0) (by omega)
  simp at h
  omega

/-- The actual cubic piece has the Euler dimension used in the outer map. -/
theorem degreeThree_euler (ht : 2 ≤ t) :
    Module.finrank K (Cokernel K t w 2) + (t + 2) * (t + w + 1).choose 2 =
      3 * (t + w + 2).choose 3 := by
  simpa [Nat.add_assoc] using cokernel_euler (K := K) (w := w) ht (j := 2) (by omega)

/-- The three surviving free-variable layers have exactly the cubic Euler count. -/
theorem free_cubic_count (t w : ℕ) (ht : 2 ≤ t) :
    3 * (t + w + 2).choose 3 = (t + 2) * (t + w + 1).choose 2 +
      t.choose 2 * w + 2 * (t - 1) * (w + 1).choose 2 + 3 * (w + 2).choose 3 := by
  have hmain := Counts.b3_scaled (t + w)
  have hquad := Counts.b2_scaled (t + w)
  have hcore := Counts.choose_two_scaled t
  have hfree2 := Counts.b2_scaled w
  have hfree3 := Counts.b3_scaled w
  unfold Counts.b2 Counts.b3 at *
  push_cast at hmain hquad
  have h : (3 : ℤ) * ((t + w + 2).choose 3 : ℤ) =
      ((t : ℤ) + 2) * ((t + w + 1).choose 2 : ℤ) +
      (t.choose 2 : ℤ) * (w : ℤ) + 2 * ((t : ℤ) - 1) * ((w + 1).choose 2 : ℤ) +
      3 * ((w + 2).choose 3 : ℤ) := by
    have h6 : (6 : ℤ) * (3 * ((t + w + 2).choose 3 : ℤ) -
        (((t : ℤ) + 2) * ((t + w + 1).choose 2 : ℤ) +
        (t.choose 2 : ℤ) * (w : ℤ) + 2 * ((t : ℤ) - 1) * ((w + 1).choose 2 : ℤ) +
        3 * ((w + 2).choose 3 : ℤ))) = 0 := by
      linear_combination 3 * hmain - 3 * ((t : ℤ) + 2) * hquad -
        3 * (w : ℤ) * hcore - 6 * ((t : ℤ) - 1) * hfree2 - 3 * hfree3
    omega
  have hsub : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
  rw [← hsub] at h
  exact_mod_cast h

/-- The actual degree-three piece has the dimension of its three surviving layers. -/
theorem degreeThree_finrank (ht : 2 ≤ t) :
    Module.finrank K (Cokernel K t w 2) =
      t.choose 2 * w + 2 * (t - 1) * (w + 1).choose 2 + 3 * (w + 2).choose 3 := by
  have he := degreeThree_euler (K := K) (w := w) ht
  have hc := free_cubic_count t w ht
  omega

end Quartic.ConvolutionFree
