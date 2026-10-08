import Quartic.FreeCoefficientProducts

/-!
# Actual homogeneous bidegree decomposition

The first `t` polynomial variables and the last `w` variables define a
bigrading. Grouping exact free-monomial coefficients gives a proved direct
product decomposition in every total degree, with explicit polynomial
insertion and extraction. Polynomial multiplication adds the two bidegrees.
-/

noncomputable section
namespace Quartic.SplitBigrading
open Module MvPolynomial FreeCoefficients FreeMonomialCounts FreeCoefficientProducts
variable {K : Type*} [Field K] {t w i j d : ℕ}

/-- A bidegree `(i,j)` polynomial, in exact Y-monomial coefficient coordinates. -/
abbrev Block (K : Type*) [Field K] (t w i j : ℕ) :=
  ExactExponent w j → Forms K t i

/-- The actual polynomial represented by one bidegree block. -/
def blockPolynomial : Block K t w i j →ₗ[K] Poly K (t + w) :=
  ∑ b : ExactExponent w j, (liftCoeff b.val).comp ((Forms K t i).subtype.comp (LinearMap.proj b))

@[simp] theorem blockPolynomial_apply (u : Block K t w i j) :
    blockPolynomial u = ∑ b : ExactExponent w j, liftCoeff b.val (u b).val := by
  simp [blockPolynomial]

@[simp] theorem freeCoeff_blockPolynomial (u : Block K t w i j) (b : ExactExponent w j) :
    freeCoeff b.val (blockPolynomial u) = (u b).val := by
  classical
  rw [blockPolynomial_apply, map_sum]
  simp only [freeCoeff_liftCoeff]
  have heq (e : ExactExponent w j) : e.val = b.val ↔ e = b := Subtype.ext_iff.symm
  simp_rw [heq]
  simp

theorem freeCoeff_blockPolynomial_of_degree_ne (u : Block K t w i j)
    (b : Fin w →₀ ℕ) (hb : b.degree ≠ j) : freeCoeff b (blockPolynomial u) = 0 := by
  classical
  rw [blockPolynomial_apply, map_sum]
  apply Finset.sum_eq_zero
  intro e _
  rw [freeCoeff_liftCoeff, ite_eq_right]
  intro he
  apply hb
  exact he ▸ e.property

/-- Bidegree coordinates determine their actual polynomial injectively. -/
theorem blockPolynomial_injective : Function.Injective
    (blockPolynomial (K := K) (t := t) (w := w) (i := i) (j := j)) := by
  intro u v h
  funext b
  apply Subtype.ext
  simpa only [freeCoeff_blockPolynomial] using congrArg (freeCoeff b.val) h

/-- Every represented bidegree block has the expected total homogeneous degree. -/
theorem blockPolynomial_homogeneous (u : Block K t w i j) :
    (blockPolynomial u).IsHomogeneous (i + j) := by
  rw [blockPolynomial_apply]
  apply (Forms K (t + w) (i + j)).sum_mem
  intro b _
  change (liftCoeff b.val (u b).val).IsHomogeneous (i + j)
  simpa only [b.property] using liftCoeff_homogeneous b.val (u b).val (u b).property

/-- Insert the block into its actual total-degree component. -/
def embed : Block K t w i j →ₗ[K] Forms K (t + w) (i + j) :=
  blockPolynomial.codRestrict _ blockPolynomial_homogeneous

@[simp] theorem embed_val (u : Block K t w i j) : (embed u).val = blockPolynomial u := rfl

theorem embed_injective : Function.Injective (embed (K := K) (t := t) (w := w) (i := i) (j := j)) :=
  fun _u _v h => blockPolynomial_injective (congrArg Subtype.val h)

/-- The actual subspace of forms of this bidegree. -/
def bidegreeSpace (K : Type*) [Field K] (t w i j : ℕ) : Submodule K (Forms K (t + w) (i + j)) :=
  LinearMap.range (embed (K := K) (t := t) (w := w) (i := i) (j := j))

/-- Extract a fixed Y-degree from a homogeneous polynomial. -/
def component (j : ℕ) : Forms K (t + w) d →ₗ[K] Block K t w (d - j) j where
  toFun p b := ⟨freeCoeff b.val p.val, by
    change (freeCoeff b.val p.val).IsHomogeneous (d - j)
    simpa only [b.property] using freeCoeff_homogeneous p.val p.property b.val⟩
  map_add' p q := by funext b; apply Subtype.ext; exact map_add _ _ _
  map_smul' c p := by funext b; apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem component_val (p : Forms K (t + w) d) (b : ExactExponent w j) :
    (component j p b).val = freeCoeff b.val p.val := rfl

/-- All bidegree components in a fixed total degree. -/
abbrev Components (K : Type*) [Field K] (t w d : ℕ) :=
  ∀ j : Fin (d + 1), Block K t w (d - j.val) j.val

/-- Split into the `d+1` bidegrees `(d-j,j)`. -/
def split : Forms K (t + w) d →ₗ[K] Components K t w d :=
  LinearMap.pi (fun j => component j.val)

/-- Reconstruct the actual homogeneous polynomial from its bidegree components. -/
def join : Components K t w d →ₗ[K] Forms K (t + w) d where
  toFun u := ⟨∑ j : Fin (d + 1), blockPolynomial (u j), by
    apply (Forms K (t + w) d).sum_mem
    intro j _
    change (blockPolynomial (u j)).IsHomogeneous d
    have h := blockPolynomial_homogeneous (u j)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)] using h⟩
  map_add' u v := by apply Subtype.ext; simp [map_add, Finset.sum_add_distrib]
  map_smul' c u := by apply Subtype.ext; simp [map_smul, Finset.smul_sum]

@[simp] theorem join_val (u : Components K t w d) :
    (join u).val = ∑ j : Fin (d + 1), blockPolynomial (u j) := rfl

/-- Different Y-degrees do not interfere under extraction. -/
theorem split_join (u : Components K t w d) : split (join u) = u := by
  classical
  funext j b
  apply Subtype.ext
  change freeCoeff b.val (join u).val = (u j b).val
  rw [join_val, map_sum, Finset.sum_eq_single j]
  · exact freeCoeff_blockPolynomial (u j) b
  · intro k _ hkj
    exact freeCoeff_blockPolynomial_of_degree_ne (u k) b.val (by
      rw [b.property]
      exact fun h => hkj (Fin.ext h.symm))
  · simp

/-- A homogeneous polynomial is determined by its bidegree components. -/
theorem split_injective : Function.Injective (split (K := K) (t := t) (w := w) (d := d)) := by
  intro p q h
  apply Subtype.ext
  have hz : p.val - q.val = 0 := by
    apply eq_zero_of_freeCoeff
    intro b
    rw [map_sub]
    by_cases hb : b.degree ≤ d
    · have he := congrArg (fun u : Components K t w d =>
        (u ⟨b.degree, by omega⟩ ⟨b, rfl⟩).val) h
      exact sub_eq_zero.mpr he
    · rw [freeCoeff_eq_zero_of_degree_lt p.val p.property b (by omega),
        freeCoeff_eq_zero_of_degree_lt q.val q.property b (by omega), sub_self]
  exact sub_eq_zero.mp hz

theorem join_split (p : Forms K (t + w) d) : join (split p) = p :=
  split_injective (split_join (split p))

/-- Actual bidegree direct-product decomposition in every homogeneous degree. -/
def homogeneousBigrading : Forms K (t + w) d ≃ₗ[K] Components K t w d :=
  { split with
    invFun := join
    left_inv := join_split
    right_inv := split_join }

/-- In degree four this is the five actual target components of the split complex. -/
def quarticBigrading (K : Type*) [Field K] (m : ℕ) :
    Forms K (3 + m) 4 ≃ₗ[K] Components K 3 m 4 := homogeneousBigrading

/-- The full coefficient source splits into its actual bidegree coefficients,
for every ordered family of quadratic generators. -/
def coefficientBigrading (r : ℕ) :
    (Fin r → Forms K (t + w) 2) ≃ₗ[K] (Fin r → Components K t w 2) :=
  LinearEquiv.piCongrRight (fun _ => homogeneousBigrading)

@[simp] theorem coefficientBigrading_apply (r : ℕ) (a : Fin r → Forms K (t + w) 2)
    (k : Fin r) (j : Fin 3) (b : ExactExponent w j.val) :
    (coefficientBigrading r a k j b).val = freeCoeff b.val (a k).val := rfl

/-- Products of two represented blocks are the sum of the actual products
with added Y exponents and multiplied X coefficient polynomials. -/
theorem blockPolynomial_mul {i' j' : ℕ} (u : Block K t w i j) (v : Block K t w i' j') :
    blockPolynomial u * blockPolynomial v =
      ∑ b : ExactExponent w j, ∑ c : ExactExponent w j',
        liftCoeff (b.val + c.val) ((u b).val * (v c).val) := by
  rw [blockPolynomial_apply, blockPolynomial_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact liftCoeff_mul b.val c.val (u b).val (v c).val

/-- Multiplication cannot create a Y-degree other than the sum of input Y-degrees. -/
theorem product_freeCoeff_eq_zero {i' j' : ℕ} (u : Block K t w i j) (v : Block K t w i' j')
    (e : Fin w →₀ ℕ) (he : e.degree ≠ j + j') :
    freeCoeff e (blockPolynomial u * blockPolynomial v) = 0 := by
  classical
  rw [blockPolynomial_mul, map_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [freeCoeff_liftCoeff, ite_eq_right]
  intro h
  apply he
  rw [← h, map_add, b.property, c.property]

/-- Actual product coordinates in the sum bidegree. -/
def blockProduct {i' j' : ℕ} (u : Block K t w i j) (v : Block K t w i' j') :
    Block K t w (i + i') (j + j') := fun e =>
  ⟨freeCoeff e.val (blockPolynomial u * blockPolynomial v), by
    change (freeCoeff e.val (blockPolynomial u * blockPolynomial v)).IsHomogeneous (i + i')
    have h := freeCoeff_homogeneous (blockPolynomial u * blockPolynomial v)
      ((blockPolynomial_homogeneous u).mul (blockPolynomial_homogeneous v)) e.val
    simpa only [e.property, show (i + j + (i' + j')) - (j + j') = i + i' by omega] using h⟩

/-- Reconstructing product coordinates is exactly multiplication in the full ring. -/
theorem blockProduct_polynomial {i' j' : ℕ} (u : Block K t w i j) (v : Block K t w i' j') :
    blockPolynomial (blockProduct u v) = blockPolynomial u * blockPolynomial v := by
  apply sub_eq_zero.mp
  apply eq_zero_of_freeCoeff
  intro e
  rw [map_sub]
  by_cases he : e.degree = j + j'
  · rw [freeCoeff_blockPolynomial (blockProduct u v) ⟨e, he⟩]
    exact sub_self _
  · rw [freeCoeff_blockPolynomial_of_degree_ne _ e he, product_freeCoeff_eq_zero u v e he,
      sub_self]

/-- The bidegree block has the product of the two symmetric-power dimensions. -/
theorem block_finrank : finrank K (Block K t w i j) =
    (t + i - 1).choose i * (w + j - 1).choose j := by
  let : Module.Free K (Forms K t i) := Module.Free.of_basis (formsBasis K t i)
  simp only [Block, Module.finrank_pi_fintype, finrank_forms, Finset.sum_const,
    Finset.card_univ, exactExponent_card, smul_eq_mul, Nat.mul_comm]

/-- The actual bidegree subspace has the same dimension as its coefficient model. -/
theorem bidegreeSpace_finrank : finrank K (bidegreeSpace K t w i j) =
    (t + i - 1).choose i * (w + j - 1).choose j := by
  rw [bidegreeSpace, LinearMap.finrank_range_of_inj embed_injective, block_finrank]

end Quartic.SplitBigrading
