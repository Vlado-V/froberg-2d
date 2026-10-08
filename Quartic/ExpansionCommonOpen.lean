import Quartic.ConvolutionExpansionOpen
import Quartic.EndpointF13AllRange

/-!
# One actual open for expansion and all checked block conditions

The dimension-zero expansion bound forces exact presentation ranks.
The actual quotient then inherits every image threshold, while polynomial
intersection places these bounds on the same mixed, child, and motion
coefficients as the checked block, cubic, and F13 conditions.
-/
noncomputable section
namespace Quartic.ExpansionCommonOpen
open Module MvPolynomial RowMultiplicationCoordinates RowExpansionOpen
open UniformEndpoint ProfileCertificate
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {m c q d e : ℕ}

theorem presentation_eq_tupleMap (g : Fin c → Rows K m 1) :
    GeneralF13.multiplication g = BilinearImage.tupleMap multiplication g := by
  apply LinearMap.ext
  intro u
  funext r
  apply Subtype.ext
  simp only [GeneralF13.multiplication_val,BilinearImage.tupleMap_apply,
    Finset.sum_apply,Submodule.coe_sum,multiplication_val]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem presentation_range (g : Fin c → Rows K m 1) :
    LinearMap.range (GeneralF13.multiplication g) =
      BilinearImage.image multiplication (Submodule.span K (Set.range g)) := by
  rw [presentation_eq_tupleMap,BilinearImage.range_tupleMap]

theorem coefficientSource_finrank : finrank K (Fin c → Forms K m 2) = c*(m+1).choose 2 := by
  simp only [Module.finrank_pi_fintype,finrank_quadrics,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]

theorem image_span_finrank_le (g : Fin c → Rows K m 1) :
    finrank K (BilinearImage.image multiplication (Submodule.span K (Set.range g))) ≤
      c*(m+1).choose 2 := by
  rw [← presentation_range]
  have h := (GeneralF13.multiplication g).finrank_range_add_finrank_ker
  rw [coefficientSource_finrank] at h
  exact (Nat.le_add_right _ _).trans_eq h

/-- The included d=0 expansion bound forces exact target relation dimension. -/
theorem relation_finrank_of_zero_expansion (g : Fin c → Rows K m 1)
    (hg : LinearIndependent K g) (e₀ : ℕ)
    (hzero : RowExpansionOpen.Expands g c (e₀+c*(m+1).choose 2)) :
    finrank K (BilinearImage.image multiplication (Submodule.span K (Set.range g))) =
      c*(m+1).choose 2 := by
  have hd : finrank K (Submodule.span K (Set.range g)) = c := by
    rw [finrank_span_eq_card hg,Fintype.card_fin]
  have hlo := hzero (Submodule.span K (Set.range g)) le_rfl hd
  have hhi := image_span_finrank_le g
  omega

/-- It also forces actual coefficient-degree-two presentation injectivity. -/
theorem presentation_injective_of_zero_expansion (g : Fin c → Rows K m 1)
    (hg : LinearIndependent K g) (e₀ : ℕ)
    (hzero : RowExpansionOpen.Expands g c (e₀+c*(m+1).choose 2)) :
    Function.Injective (GeneralF13.multiplication g) := by
  have hd := relation_finrank_of_zero_expansion g hg e₀ hzero
  rw [← presentation_range] at hd
  have h := (GeneralF13.multiplication g).finrank_range_add_finrank_ker
  rw [coefficientSource_finrank,hd] at h
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.finrank_eq_zero.mp (by omega)

theorem cubic_quotient_dimension (g : Fin c → Rows K m 1)
    (hg : LinearIndependent K g) (e₀ : ℕ)
    (hzero : RowExpansionOpen.Expands g c (e₀+c*(m+1).choose 2)) :
    finrank K ((Rows K m 3) ⧸ BilinearImage.image multiplication (Submodule.span K (Set.range g))) =
      3*(m+2).choose 3-c*(m+1).choose 2 := by
  have h := (BilinearImage.image multiplication (Submodule.span K (Set.range g))).finrank_quotient_add_finrank
  rw [relation_finrank_of_zero_expansion g hg e₀ hzero] at h
  have hd : finrank K (Rows K m 3) = 3*(m+2).choose 3 := by
    simp [Rows,Module.finrank_pi_fintype,finrank_forms]
  rw [hd] at h
  omega

theorem linear_quotient_dimension (g : Fin c → Rows K m 1)
    (hg : LinearIndependent K g) :
    finrank K ((Rows K m 1) ⧸ Submodule.span K (Set.range g)) = 3*m-c := by
  have h := (Submodule.span K (Set.range g)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hg,Fintype.card_fin] at h
  have hd : finrank K (Rows K m 1) = 3*m := by
    simp [Rows,Module.finrank_pi_fintype,finrank_forms]
  rw [hd] at h
  omega

/-- Actual quotient images inherit the ambient bound after the exact shifts. -/
theorem quotient_expansion (g : Fin c → Rows K m 1) (hg : LinearIndependent K g)
    (e₀ : ℕ) (hzero : RowExpansionOpen.Expands g c (e₀+c*(m+1).choose 2))
    (hbound : RowExpansionOpen.Expands g (d+c) (e+c*(m+1).choose 2)) :
    ∀ S : Submodule K ((Rows K m 1) ⧸ Submodule.span K (Set.range g)), finrank K S = d →
      e ≤ finrank K (BilinearImage.image
        (QuotientBilinearImage.quotientMap multiplication (Submodule.span K (Set.range g))) S) := by
  apply (QuotientBilinearImage.expansion_iff_ambient multiplication
    (Submodule.span K (Set.range g)) d e).mpr
  have hd : finrank K (Submodule.span K (Set.range g)) = c := by
    rw [finrank_span_eq_card hg,Fintype.card_fin]
  rw [hd,relation_finrank_of_zero_expansion g hg e₀ hzero]
  exact hbound

def ExpansionOpen (M : ℕ) (upper : Bool) (m c q : ℕ) : Prop :=
  ∃ E : ConvolutionExpansionOpen.Dimensions M upper → ℕ,
    ConvolutionExpansionOpen.Thresholds M upper E ∧
    ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m c q) K,
      (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
        ∀ d : ConvolutionExpansionOpen.Dimensions M upper,
          RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
            (d.val+mixedCount M upper) (E d+mixedCount M upper*(M+1).choose 2)

include L in
theorem expansion_augmented (m : ℕ) (hm : 41 ≤ m) (upper : Bool) :
    ExpansionOpen (K := K) m upper m (mixedCount m upper) (upperEndpoint m) := by
  let t := coreP (mixedCount m upper)+1
  let w := freeW m (mixedCount m upper)
  let q := upperEndpoint m
  let g := fun p : AugmentedGeneric.ParameterIndex (t+w) (t+2) q → K =>
    AugmentedGeneric.coefficientMixed p
  let p₀ := AugmentedGeneric.encode (GenericF13Endpoint.convolutionMixed K t w)
    (0 : Fin q → Forms K (t+w) 2) 0
  have hp₀ : g p₀ = GenericF13Endpoint.convolutionMixed K t w :=
    AugmentedGeneric.coefficientMixed_encode _ _ _
  have hg : ∀ j, IsPolynomialFamily (fun p => g p j) :=
    fun j => isPolynomialFamily_linear ((LinearMap.proj j).comp AugmentedGeneric.coefficientMixed)
  obtain ⟨E,hE,D,hD,hgood⟩ := ConvolutionExpansionOpen.principal_open_family
    (L := L) m hm upper g hg p₀ hp₀
  have hh : ExpansionOpen (K := K) m upper (t+w) (t+2) q :=
    ⟨E,hE,D,⟨p₀,hD⟩,hgood⟩
  have hvars : t+w=m := ConvolutionOuterGeneric.endpoint_variable_count m hm upper
  have hc := ConvolutionOuterGeneric.endpoint_columns_range m hm upper
  have hcols : t+2=mixedCount m upper := by dsimp [t]; unfold coreP; omega
  simpa only [hvars,hcols,q] using hh

include L in
theorem common_open [Infinite K] (m : ℕ) (hm : 41 ≤ m) (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ E : ConvolutionExpansionOpen.Dimensions m upper → ℕ,
      ConvolutionExpansionOpen.Thresholds m upper E ∧
      ∃ D : MvPolynomial (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
        (∃ p, eval p D ≠ 0) ∧ ∀ p, eval p D ≠ 0 →
          SimultaneousBlockConditions.BlockConditions p ∧
          GenericF13.Conditions (AugmentedGeneric.coefficientMixed p) (AugmentedGeneric.coefficientChild p) ∧
          finrank K (CubicGeneric.CubicQuotient (AugmentedGeneric.coefficientChild p)) =
            (m+2).choose 3-m*upperEndpoint m ∧
          ∀ d : ConvolutionExpansionOpen.Dimensions m upper,
            RowExpansionOpen.Expands (AugmentedGeneric.coefficientMixed p)
              (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2) := by
  classical
  obtain ⟨E,hE,A,⟨a,ha⟩,hA⟩ := expansion_augmented (K := K) (L := L) m hm upper
  obtain ⟨B,⟨b,hb⟩,hB⟩ := EndpointF13AllRange.generic_endpoint_conditions (K := K) m (by omega) upper h2
  have hA0 : A ≠ 0 := by intro h; simp [h] at ha
  have hB0 : B ≠ 0 := by intro h; simp [h] at hb
  obtain ⟨p₀,hp₀⟩ := nonempty_principal_intersection
    (![A,B] : Fin 2 → MvPolynomial
      (AugmentedGeneric.ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨E,hE,A*B,⟨p₀,?_⟩,?_⟩
  · rw [map_mul]
    exact mul_ne_zero (hp₀ 0) (hp₀ 1)
  · intro p hp
    rw [map_mul,mul_ne_zero_iff] at hp
    obtain ⟨hb,hf,hc⟩ := hB p hp.2
    exact ⟨hb,hf,hc,hA p hp.1⟩

end Quartic.ExpansionCommonOpen

