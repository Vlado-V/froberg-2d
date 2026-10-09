module

public import Froberg.GenericDivisibility
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-! Equivariant divisibility over arbitrary infinite fields.

The central-weight argument applies to every divisor whose order is nonzero
in the coefficient field.  Its maximal such divisor is the part prime to the
characteristic; in characteristic zero this is the original integer. -/
noncomputable section
namespace Froberg
open Matrix Module MvPolynomial

variable {K : Type*} [Field K] [Infinite K] {n d r ℓ : ℕ}

/-- A root of unity of any order dividing the central stabilizer gives the
corresponding divisor of the actual generic cokernel. -/
theorem genericCokernel_divisibility_of_divisor_primitiveRoot (hn : 0<n)
    (hℓ : ℓ∣Nat.gcd n (d*r)) (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) :
    ℓ∣(2*d)*genericCokernel K n d r := by
  classical
  let R := MvPolynomial (CoefficientIndex n d r) K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let ι : K →+* F := φ.comp C
  have hℓn : ℓ∣n := hℓ.trans (Nat.gcd_dvd_left _ _)
  have hℓr : ℓ∣d*r := hℓ.trans (Nat.gcd_dvd_right _ _)
  have hℓpos : 0<ℓ := Nat.pos_of_dvd_of_pos hℓn hn
  have hz0 : ζ≠0 := hζ.ne_zero hℓpos.ne'
  have hzn : ζ^n=1 := (hζ.pow_eq_one_iff_dvd n).mpr hℓn
  have hzr : (ζ^d)^r=1 := by
    rw [←pow_mul]
    exact (hζ.pow_eq_one_iff_dvd (d*r)).mpr hℓr
  let z := (scalarSL n ζ hzn,scalarSL r (ζ^d) hzr)
  let M := (universalMultiplicationMatrix K n d r).map φ
  have hroot : IsPrimitiveRoot (ι ζ) ℓ := hζ.map_of_injective ι.injective
  have hmat : ((universalTargetAction (d := d)).matrix z).map φ =
      (ι ζ)^(2*d) • (1 : Matrix (Fin (finrank K (Forms K n (2*d))))
        (Fin (finrank K (Forms K n (2*d)))) F) := by
    rw [central_pair_target_matrix]
    apply Matrix.ext
    intro i j
    by_cases hij : i=j <;> simp [Matrix.smul_apply,Matrix.one_apply,ι,φ,hij]
  have himage := invariant_subspace_weight_divisibility (universalTargetAction (d := d))
    (LinearMap.range M.mulVecLin)
    (fun g w hw => universalMultiplication_image_invariant g w hw)
    z (central_pair_coefficient_action ζ hz0 hzn hzr) hroot hmat
  have htotal := hℓn.trans (variables_dvd_degree_mul_monomials n (2*d))
  have hdim := genericCokernel_add_fraction_rank K n d r F hn
  rw [←hdim,Nat.mul_add] at htotal
  exact (Nat.dvd_add_iff_left himage).mpr htotal

/-- A divisor prime to the field characteristic has enough roots after base
extension, and the resulting rank divisibility descends to the original field. -/
theorem genericCokernel_divisibility_of_cast_ne_zero (hn : 0<n)
    (hℓ : ℓ∣Nat.gcd n (d*r)) (hne : (ℓ : K)≠0) :
    ℓ∣(2*d)*genericCokernel K n d r := by
  letI : NeZero (ℓ : K) := ⟨hne⟩
  let L := AlgebraicClosure K
  obtain ⟨ζ,hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L ℓ
  have h := genericCokernel_divisibility_of_divisor_primitiveRoot (K := L) hn hℓ ζ hζ
  rwa [←GenericFieldDescent.genericCokernel_baseChange (algebraMap K L) hn] at h

/-- The integral Euler identity transfers any divisor of the central order
from the generic cokernel to the generic first homology. -/
theorem genericHomology_divisor_of_genericCokernel (hn : 0<n)
    (hr : r≤(n+d-1).choose d) (hℓ : ℓ∣Nat.gcd n (d*r))
    (hc : ℓ∣(2*d)*genericCokernel K n d r) :
    ℓ∣(2*d)*genericHomology K n d r := by
  have hc' : (ℓ : ℤ)∣(2*d : ℤ)*(genericCokernel K n d r : ℤ) := by exact_mod_cast hc
  have hℓ' : (ℓ : ℤ)∣(Nat.gcd n (d*r) : ℤ) := by exact_mod_cast hℓ
  have he := hℓ'.trans (gcd_dvd_weighted_euler n d r)
  have hid := generic_euler (K := K) hn hr
  have hh : (ℓ : ℤ)∣(2*d : ℤ)*(genericHomology K n d r : ℤ) := by
    convert dvd_sub hc' he using 1
    rw [←hid]
    ring
  exact_mod_cast hh

theorem genericHomology_divisibility_of_cast_ne_zero (hn : 0<n)
    (hr : r≤(n+d-1).choose d) (hℓ : ℓ∣Nat.gcd n (d*r)) (hne : (ℓ : K)≠0) :
    ℓ∣(2*d)*genericHomology K n d r :=
  genericHomology_divisor_of_genericCokernel hn hr hℓ
    (genericCokernel_divisibility_of_cast_ne_zero hn hℓ hne)

/-- A positive integer is nonzero in the field when its prime divisors avoid
the characteristic.  The zero-characteristic case is stated separately. -/
theorem natCast_ne_zero_of_characteristic_coprime (hℓ : 0<ℓ)
    (hchar : ringChar K=0 ∨ Nat.Coprime ℓ (ringChar K)) : (ℓ : K)≠0 := by
  intro hzero
  have hdvd : ringChar K∣ℓ := (ringChar.spec K ℓ).mp hzero
  rcases hchar with hchar | hchar
  · rw [hchar] at hdvd
    have : ℓ=0 := Nat.zero_dvd.mp hdvd
    omega
  · have hone : ringChar K=1 := by
      simpa only [Nat.Coprime,Nat.gcd_eq_right hdvd] using hchar
    exact CharP.ringChar_ne_one hone

/-- Form used by the field-uniform arithmetic argument. -/
theorem generic_defects_divisibility_of_characteristic_coprime (hn : 0<n)
    (hr : r≤(n+d-1).choose d) (hℓ : ℓ∣Nat.gcd n (d*r))
    (hchar : ringChar K=0 ∨ Nat.Coprime ℓ (ringChar K)) :
    ℓ∣(2*d)*genericHomology K n d r ∧ ℓ∣(2*d)*genericCokernel K n d r := by
  have hℓpos : 0<ℓ := Nat.pos_of_dvd_of_pos
    (hℓ.trans (Nat.gcd_dvd_left _ _)) hn
  have hne := natCast_ne_zero_of_characteristic_coprime (K := K) hℓpos hchar
  exact ⟨genericHomology_divisibility_of_cast_ne_zero hn hr hℓ hne,
    genericCokernel_divisibility_of_cast_ne_zero hn hℓ hne⟩

/-- The part of an integer prime to the field characteristic. For
characteristic zero, `ordCompl[0] m` is simply `m`. -/
def primeToCharacteristicPart (K : Type*) [Field K] (m : ℕ) : ℕ :=
  ordCompl[ringChar K] m

theorem primeToCharacteristicPart_dvd (m : ℕ) :
    primeToCharacteristicPart K m∣m := Nat.ordCompl_dvd _ _

theorem primeToCharacteristicPart_pos {m : ℕ} (hm : 0<m) :
    0<primeToCharacteristicPart K m := Nat.ordCompl_pos _ hm.ne'

theorem primeToCharacteristicPart_eq_of_charZero [CharZero K] (m : ℕ) :
    primeToCharacteristicPart K m=m := by
  unfold primeToCharacteristicPart
  rw [ringChar.eq_zero]
  exact Nat.ordCompl_of_not_prime m 0 (by decide)

theorem primeToCharacteristicPart_cast_ne_zero {m : ℕ} (hm : 0<m) :
    (primeToCharacteristicPart K m : K)≠0 := by
  apply natCast_ne_zero_of_characteristic_coprime (primeToCharacteristicPart_pos hm)
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · exact Or.inr (Nat.coprime_ordCompl hp hm.ne').symm
  · exact Or.inl hp

/-- Every divisor nonzero in the field divides the prime-to-characteristic
part, giving its maximality in the sense needed by Lemma 7.1. -/
theorem dvd_primeToCharacteristicPart {m : ℕ} (hℓm : ℓ∣m) (hne : (ℓ : K)≠0) :
    ℓ∣primeToCharacteristicPart K m :=
  Nat.dvd_ordCompl_of_dvd_not_dvd hℓm (fun h => hne ((ringChar.spec K ℓ).mpr h))

/-- Lemma 7.1, with the largest prime-to-characteristic divisor, for every
infinite coefficient field. -/
theorem generic_defects_primeToCharacteristic_divisibility (hn : 0<n)
    (hr : r≤(n+d-1).choose d) :
    primeToCharacteristicPart K (Nat.gcd n (d*r))∣(2*d)*genericHomology K n d r ∧
    primeToCharacteristicPart K (Nat.gcd n (d*r))∣(2*d)*genericCokernel K n d r := by
  have hpos := Nat.gcd_pos_of_pos_left (d*r) hn
  have hdiv := primeToCharacteristicPart_dvd (K := K) (Nat.gcd n (d*r))
  have hne := primeToCharacteristicPart_cast_ne_zero (K := K) hpos
  exact ⟨genericHomology_divisibility_of_cast_ne_zero hn hr hdiv hne,
    genericCokernel_divisibility_of_cast_ne_zero hn hdiv hne⟩

end Froberg
