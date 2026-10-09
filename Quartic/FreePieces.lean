module

public import Quartic.FreeCoefficients

@[expose] public section

/-!
# The actual homogeneous decomposition by free monomials

Each homogeneous polynomial in `t+w` variables is the finite sum of its
free-monomial coefficients. This gives a canonical linear equivalence, with
explicit coefficient extraction and reconstruction, in every degree.
-/

noncomputable section
namespace Quartic.FreeCoefficients
open MvPolynomial
variable {K : Type*} [Field K] {t w d : ℕ}

/-- The free monomials that can occur in total degree `d`. -/
abbrev BoundedExponent (w d : ℕ) := {b : Fin w →₀ ℕ // b.degree ≤ d}

instance boundedExponentFinite : Finite (BoundedExponent w d) := by
  let f : BoundedExponent w d → Fin w → Fin (d + 1) := fun b i =>
    ⟨b.val i, lt_of_le_of_lt ((Finsupp.le_degree i b.val).trans b.property) (Nat.lt_succ_self d)⟩
  apply Finite.of_injective f
  intro b e h
  apply Subtype.ext
  ext i
  exact congrArg (fun v : Fin w → Fin (d + 1) => (v i).val) h

noncomputable instance boundedExponentFintype : Fintype (BoundedExponent w d) :=
  Fintype.ofFinite _

/-- Coefficients in the core homogeneous spaces, indexed by free monomials. -/
abbrev Pieces (K : Type*) [Field K] (t w d : ℕ) :=
  ∀ b : BoundedExponent w d, Quartic.Forms K t (d - b.val.degree)

/-- Split a homogeneous polynomial into all its free-monomial coefficients. -/
def split : Quartic.Forms K (t + w) d →ₗ[K] Pieces K t w d :=
  LinearMap.pi fun b => homogeneousCoeff b.val

@[simp] theorem split_apply_val (p : Quartic.Forms K (t + w) d)
    (b : BoundedExponent w d) : (split p b).val = freeCoeff b.val p.val := rfl

/-- Insert a component back into the original homogeneous polynomial space. -/
def homogeneousLift (b : BoundedExponent w d) :
    Quartic.Forms K t (d - b.val.degree) →ₗ[K] Quartic.Forms K (t + w) d :=
  ((liftCoeff b.val).comp (Quartic.Forms K t (d - b.val.degree)).subtype).codRestrict _
    (fun p => by
      change (liftCoeff b.val p.val).IsHomogeneous d
      have h := liftCoeff_homogeneous b.val p.val p.property
      simpa only [Nat.sub_add_cancel b.property] using h)

@[simp] theorem homogeneousLift_apply_val (b : BoundedExponent w d)
    (p : Quartic.Forms K t (d - b.val.degree)) :
    (homogeneousLift b p).val = liftCoeff b.val p.val := rfl

/-- Reconstruct the polynomial by summing its inserted coefficient components. -/
def join : Pieces K t w d →ₗ[K] Quartic.Forms K (t + w) d :=
  ∑ b : BoundedExponent w d, (homogeneousLift b).comp (LinearMap.proj b)

@[simp] theorem join_apply_val (v : Pieces K t w d) :
    (join v).val = ∑ b : BoundedExponent w d, liftCoeff b.val (v b).val := by
  simp [join]

/-- Every coefficient is recovered exactly after reconstruction. -/
theorem split_join (v : Pieces K t w d) : split (join v) = v := by
  classical
  funext b
  apply Subtype.ext
  simp only [split_apply_val, join_apply_val, map_sum, freeCoeff_liftCoeff]
  have heq (e : BoundedExponent w d) : (e.val = b.val) ↔ e = b := Subtype.ext_iff.symm
  simp_rw [heq]
  simp

/-- Coefficient extraction determines a homogeneous polynomial completely. -/
theorem split_injective : Function.Injective (split (K := K) (t := t) (w := w) (d := d)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  change p = 0
  apply Subtype.ext
  apply eq_zero_of_freeCoeff
  intro b
  by_cases hb : b.degree ≤ d
  · have h := congrArg (fun v : Pieces K t w d => (v ⟨b, hb⟩).val) hp
    simpa using h
  · exact freeCoeff_eq_zero_of_degree_lt p.val p.property b (by omega)

theorem join_split (p : Quartic.Forms K (t + w) d) : join (split p) = p :=
  split_injective (split_join (split p))

/-- Canonical homogeneous decomposition over every field and for every `t,w,d`. -/
def homogeneousPiecesEquiv : Quartic.Forms K (t + w) d ≃ₗ[K] Pieces K t w d :=
  { split with
    invFun := join
    left_inv := join_split
    right_inv := split_join }

end Quartic.FreeCoefficients
