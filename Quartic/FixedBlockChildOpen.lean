module

public import Quartic.ActualExpansionSlices
public import Quartic.SharedChildFlag

@[expose] public section

/-!
# Child flags and all block conditions with the mixed presentation fixed

A point on the actual common expansion/block open determines a fixed mixed
family and fixed pure motions. Substitution of only the child coefficients
pulls its determinant back to an actual nonempty child-coordinate open.
Intersecting with the upper-child flag open preserves every expansion
threshold and every block, cubic, and F13 condition on the same child family.
-/
noncomputable section
namespace Quartic.FixedBlockChildOpen
open Module MvPolynomial RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open UniformEndpoint AugmentedGeneric
variable {K : Type*} [Field K] {m c q : ℕ}
set_option maxHeartbeats 1000000

abbrev ChildIndex (m q : ℕ) := Fin q × Fin (FormCount m 2)

def decode : (ChildIndex m q → K) →ₗ[K] (Fin q → Forms K m 2) :=
  LinearMap.pi fun i => finiteEquiv.symm.toLinearMap.comp
    (LinearMap.funLeft K K (fun j => (i,j)))

def encodeChild (h : Fin q → Forms K m 2) : ChildIndex m q → K :=
  fun i => finiteEquiv (h i.1) i.2

@[simp] theorem decode_encode (h : Fin q → Forms K m 2) : decode (encodeChild h) = h := by
  funext i
  exact finiteEquiv.symm_apply_apply (h i)

@[simp] theorem encode_decode (a : ChildIndex m q → K) : encodeChild (decode a) = a := by
  funext i
  exact congrFun (finiteEquiv.apply_symm_apply (fun j => a (i.1,j))) i.2

theorem decode_surjective : Function.Surjective (decode (K := K) (m := m) (q := q)) :=
  fun h => ⟨encodeChild h,decode_encode h⟩

/-- The original full coefficient point is recovered from its actual three families. -/
theorem encode_recover (a : ParameterIndex m c q → K) :
    encode (coefficientMixed a) (coefficientChild a) (coefficientMotions a) = a := by
  funext i
  cases i with
  | inl j =>
    change MiddleCoordinates.decode.symm (MiddleCoordinates.decode (fun j => a (Sum.inl j))) j = _
    rw [LinearEquiv.symm_apply_apply]
  | inr j =>
    change (formsBasis K m 2).equivFun ((formsBasis K m 2).equivFun.symm
      (fun s => a (Sum.inr (j.1,s)))) j.2 = _
    rw [LinearEquiv.apply_symm_apply]

/-- With mixed coefficients and motions fixed, every original coefficient is polynomial in child coordinates. -/
theorem coordinate_polynomial (g : Fin c → MiddleCoordinates.Mixed K m)
    (r : Fin 4 → Forms K m 2) (j : ParameterIndex m c q) :
    ∃ P : MvPolynomial (ChildIndex m q) K,
      ∀ a, eval a P = encode g (decode a) r j := by
  have hbase : IsPolynomialFamily (fun a : ChildIndex m q → K => (g,decode a)) :=
    (isPolynomialFamily_const g).prod_mk (isPolynomialFamily_linear decode)
  cases j with
  | inl j =>
    exact (hbase.linear_comp ((LinearMap.proj j).comp
      MiddleCoordinates.decode.symm.toLinearMap)) LinearMap.id
  | inr j =>
    exact ⟨C ((formsBasis K m 2).equivFun (r j.1) j.2),fun a => by simp [encode]⟩

def coordinatePolynomial (g : Fin c → MiddleCoordinates.Mixed K m)
    (r : Fin 4 → Forms K m 2) (j : ParameterIndex m c q) :
    MvPolynomial (ChildIndex m q) K := Classical.choose (coordinate_polynomial g r j)

@[simp] theorem eval_coordinatePolynomial (g : Fin c → MiddleCoordinates.Mixed K m)
    (r : Fin 4 → Forms K m 2) (a : ChildIndex m q → K) (j : ParameterIndex m c q) :
    eval a (coordinatePolynomial g r j) = encode g (decode a) r j :=
  Classical.choose_spec (coordinate_polynomial g r j) a

def pullback (g : Fin c → MiddleCoordinates.Mixed K m) (r : Fin 4 → Forms K m 2)
    (D : MvPolynomial (ParameterIndex m c q) K) : MvPolynomial (ChildIndex m q) K :=
  aeval (coordinatePolynomial g r) D

@[simp] theorem eval_pullback (g : Fin c → MiddleCoordinates.Mixed K m)
    (r : Fin 4 → Forms K m 2) (D : MvPolynomial (ParameterIndex m c q) K)
    (a : ChildIndex m q → K) : eval a (pullback g r D) = eval (encode g (decode a) r) D := by
  rw [pullback,← PolynomialImageAvoidance.eval_polynomialMap]
  have he : PolynomialImageAvoidance.polynomialMap (coordinatePolynomial g r) a =
      encode g (decode a) r := by
    funext i
    exact eval_coordinatePolynomial g r a i
  rw [he]

/-- Fix one mixed presentation on the common expansion locus. One child-only principal open
then preserves all block conditions and imposes the actual upper-child flag. -/
theorem exists_fixed_open [CharZero K] [IsAlgClosed K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool)
    (hchild : ∀ s,s ≤ (m+1).choose 2 → GenericQuartic K m s) :
    ∃ g : Fin (mixedCount m upper) → Rows K m 1,
    ∃ r : Fin 4 → Forms K m 2,
    ∃ E : ConvolutionExpansionOpen.Dimensions m upper → ℕ,
      ConvolutionExpansionOpen.Thresholds m upper E ∧ LinearIndependent K g ∧
      (∀ d : ConvolutionExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
        (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2)) ∧
      ∃ D : MvPolynomial (ChildIndex m (upperEndpoint m)) K,
        (∃ a,eval a D ≠ 0) ∧ ∀ a,eval a D ≠ 0 →
          SimultaneousBlockConditions.BlockConditions (encode g (decode a) r) ∧
          GenericF13.Conditions g (decode a) ∧
          finrank K (CubicGeneric.CubicQuotient (decode a)) = (m+2).choose 3-m*upperEndpoint m ∧
          SharedChildFlag.Data (decode a) := by
  classical
  obtain ⟨E,hE,D,⟨p₀,hp₀⟩,hD⟩ := ExpansionCommonOpen.common_open (K := K) (L := K)
    m hm upper (by norm_num)
  let g := coefficientMixed p₀
  let r := coefficientMotions p₀
  obtain ⟨hblock₀,hf₀,hc₀,hexp⟩ := hD p₀ hp₀
  let B := pullback g r D
  have hB : ∃ a,eval a B ≠ 0 := by
    refine ⟨encodeChild (coefficientChild p₀),?_⟩
    simpa only [B,eval_pullback,decode_encode,g,r,encode_recover] using hp₀
  obtain ⟨A,hA,hflag⟩ := SharedChildFlag.endpoint_principal_open (K := K) (by omega : 1 ≤ m)
    (upperEndpoint m) rfl decode (isPolynomialFamily_linear decode) decode_surjective hchild
  have hBn : B ≠ 0 := by obtain ⟨a,ha⟩ := hB; intro hz; simp [hz] at ha
  have hAn : A ≠ 0 := by obtain ⟨a,ha⟩ := hA; intro hz; simp [hz] at ha
  refine ⟨g,r,E,hE,hblock₀.1.1,hexp,A*B,
    PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hAn hBn),?_⟩
  intro a ha
  rw [map_mul,mul_ne_zero_iff] at ha
  have hp : eval (encode g (decode a) r) D ≠ 0 := by
    simpa only [B,eval_pullback] using ha.2
  obtain ⟨hblock,hf,hc,_⟩ := hD _ hp
  refine ⟨hblock,?_,?_,hflag a ha.1⟩
  · simpa only [coefficientMixed_encode,coefficientChild_encode] using hf
  · have he := congrArg (fun h : Fin (upperEndpoint m) → Forms K m 2 =>
        finrank K (CubicGeneric.CubicQuotient h)) (coefficientChild_encode g (decode a) r)
    exact he.symm.trans hc

end Quartic.FixedBlockChildOpen
