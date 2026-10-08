import Froberg.RetainedSubspaceGrowth
import Froberg.PrefixGrowth

/-! Generic scalar multiplication after an arbitrary coordinate projection.
The numerical growth fraction is a parameter, so this covers both C.1 and B.4. -/
noncomputable section
namespace Froberg.ProjectedPrefix
open Module MvPolynomial MonomialExpansion
open Quartic.PolynomialBilinearCoordinates
variable {K : Type*} [Field K] {n d e r : ℕ}
variable (P : (Fin n →₀ ℕ) → Prop) [DecidablePred P]

abbrev RetainedForms (D : ℕ) := (Forms K n D).map (retainMonomials P)

def retainDegree (D : ℕ) : Forms K n D →ₗ[K] RetainedForms (K := K) P D :=
  ((retainMonomials P).comp (Forms K n D).subtype).codRestrict _
    (fun f => ⟨f.val,f.property,rfl⟩)

def bilinear : (Fin r → Forms K n e) →ₗ[K]
    (Fin r → Forms K n d) →ₗ[K] RetainedForms (K := K) P (d+e) where
  toFun a := (retainDegree P (d+e)).comp (prefixBilinear a)
  map_add' a b := by ext q; simp
  map_smul' c a := by ext q; simp

def multiplication (f : Fin r → Forms K n d) (e : ℕ) :
    (Fin r → Forms K n e) →ₗ[K] RetainedForms (K := K) P (d+e) :=
  (bilinear P).flip f

theorem multiplication_val (f : Fin r → Forms K n d) (a : Fin r → Forms K n e) :
    (multiplication P f e a).val = retainMonomials P (prefixMultiplication f e a).val := rfl

theorem scalar_product_disjoint_kernel (f : Fin r → Forms K n d)
    (hf : Function.Injective (multiplication P f e)) :
    Disjoint (familySpace f * Forms K n e) (retainMonomials (K := K) P).ker := by
  apply Submodule.disjoint_def.mpr
  intro q hq hP
  rw [← range_ambient_prefixMultiplication] at hq
  obtain ⟨a,rfl⟩ := hq
  have hz : multiplication P f e a = 0 := by
    apply Subtype.ext
    exact hP
  have ha : a=0 := hf (by simpa using hz)
  simp [ha]

theorem bilinear_rank (a : Fin r → Forms K n e) :
    finrank K (bilinear (d := d) P a).range =
      finrank K ((familySpace a * Forms K n d).map (retainMonomials P)) := by
  let L : Poly K n →ₗ[K] Poly K n := retainMonomials P
  have he : (Forms K n (d+e)).subtype.comp (prefixBilinear a) =
      (Forms K n (e+d)).subtype.comp (prefixMultiplication a d) := by
    ext q
    simp [prefixBilinear,prefixIncidenceFiber_val,prefixMultiplication_val,mul_comm]
  have hbase : ((Forms K n (d+e)).subtype.comp (prefixBilinear a)).range =
      familySpace a * Forms K n d := by rw [he,range_ambient_prefixMultiplication]
  have hr : (bilinear (d := d) P a).range.map
      (RetainedForms (K := K) P (d+e)).subtype = (familySpace a * Forms K n d).map L := by
    rw [← LinearMap.range_comp]
    change (L.comp ((Forms K n (d+e)).subtype.comp (prefixBilinear a))).range = _
    rw [LinearMap.range_comp,hbase]
  have hh := congrArg (fun U : Submodule K (Poly K n) => finrank K U) hr
  rw [Submodule.finrank_map_subtype_eq] at hh
  exact hh

/-- The full nonempty principal-open conclusion from projected subspace growth. -/
theorem generic_injective_of_growth [Infinite K] (hn : 0<n) (a b : ℕ) (hb : 0<b)
    (hgrowth : ∀ U : Submodule K (Poly K n), U ≤ Forms K n e →
      a * (n+(e+d)-1).choose (e+d) * finrank K U ≤
        b * (n+e-1).choose e * finrank K ((U * Forms K n d).map (retainMonomials P)))
    (hcount : b * (n+e-1).choose e * ((n+e-1).choose e+r) ≤
      a * (n+(e+d)-1).choose (e+d)) :
    ∃ Q : MvPolynomial (Fin (finrank K (Fin r → Forms K n d))) K,
      (∃ f : Fin r → Forms K n d, eval (coordinates K _ f) Q ≠ 0) ∧
      ∀ f : Fin r → Forms K n d, eval (coordinates K _ f) Q ≠ 0 →
        Function.Injective (multiplication P f e) := by
  apply Quartic.BilinearGeneric.generic_injective_actual (bilinear P)
  intro v hv
  dsimp only
  rw [finrank_forms K n e hn,bilinear_rank]
  let N := (n+e-1).choose e
  let k := finrank K (Submodule.span K (Set.range v))
  have hN : 0<N := monomial_count_pos hn e
  have hg := hgrowth (familySpace v) (familySpace_homogeneous v)
  rw [finrank_familySpace] at hg
  have hk : k*(N-k)+r*k ≤ k*(N+r) := by
    nlinarith [Nat.mul_le_mul_left k (Nat.sub_le N k)]
  have h : b*N*(k*(N-k)+r*k) ≤
      b*N*finrank K ((familySpace v * Forms K n d).map (retainMonomials P)) := by
    calc
      _ ≤ b*N*(k*(N+r)) := Nat.mul_le_mul_left _ hk
      _ = (b*N*(N+r))*k := by ring
      _ ≤ (a*(n+(e+d)-1).choose (e+d))*k := Nat.mul_le_mul_right k hcount
      _ ≤ _ := hg
  exact Nat.le_of_mul_le_mul_left h (by positivity)

end Froberg.ProjectedPrefix
