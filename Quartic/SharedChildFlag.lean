module

public import Quartic.MarkedCoefficient
public import Quartic.PolynomialRankOpen
public import Quartic.UniformEndpoint

@[expose] public section

/-! One actual child flag, chosen on a common principal open. -/
noncomputable section
namespace Quartic.SharedChildFlag
open Module MvPolynomial EndpointHomology
variable {K ι : Type*} [Field K] {n r : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def multiplicationLinear : (Fin r → Forms K n 2) →ₗ[K]
    ((Fin r → Forms K n 2) →ₗ[K] Forms K n 4) :=
  coefficientMultiplicationLinear.comp multiplierCoordinates.toLinearMap

@[simp] theorem multiplicationLinear_apply (q : Fin r → Forms K n 2) :
    multiplicationLinear q=quadraticMultiplication q := by
  change quadraticMultiplication (coefficientQuadrics K n r (multiplierCoordinates q))=_
  congr 1
  funext i
  exact (formsBasis K n 2).equivFun.symm_apply_apply (q i)

/-- Transport the induction hypothesis to any surjective polynomial family
of ordered child generators, including the full parent coefficient family. -/
theorem quartic_open (f : (ι → K) → (Fin r → Forms K n 2))
    (hf : IsPolynomialFamily f) (hfSurj : Function.Surjective f)
    (hgeneric : GenericQuartic K n r) :
    ∃ D : MvPolynomial ι K,(∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → LinearIndependent K (f a) ∧
        finrank K (QuarticQuotient K n
          (Submodule.span K (Set.range (fun i => (f a i).val))))=expectedDimension n r := by
  classical
  obtain ⟨D₀,⟨a₀,ha₀⟩,h₀⟩ := hgeneric
  obtain ⟨hlin,hdim⟩ := h₀ a₀ ha₀
  obtain ⟨b,hb⟩ := hfSurj (coefficientQuadrics K n r a₀)
  have hbLin : LinearIndependent K (f b) := by
    rw [hb]
    exact LinearIndependent.of_comp (Forms K n 2).subtype hlin
  obtain ⟨D₁,hD₁,h₁⟩ := independent_polynomial_principal_open
    (fun i a => f a i) (fun i => hf.linear_comp (LinearMap.proj i)) b hbLin
  obtain ⟨D₂,hD₂,h₂⟩ := rank_polynomial_principal_open
    (fun a => quadraticMultiplication (f a))
    (by simpa only [multiplicationLinear_apply] using hf.linear_comp (W := ((Fin r → Forms K n 2) →ₗ[K] Forms K n 4)) (multiplicationLinear (K := K) (n := n) (r := r))) b
  refine ⟨D₁*D₂,⟨b,by simpa only [map_mul] using mul_ne_zero hD₁ hD₂⟩,?_⟩
  intro a ha
  rw [map_mul,mul_ne_zero_iff] at ha
  have hi := h₁ a ha.1
  refine ⟨hi,?_⟩
  have hbefore := quartic_quotient_add_rank (f b)
  have hafter := quartic_quotient_add_rank (f a)
  have hr := h₂ a ha.2
  have hlo := quartic_quotient_lower_bound (f a) hi
  rw [hb] at hbefore
  change finrank K (QuarticQuotient K n (coefficientSpace K n r a₀))+_= _ at hbefore
  rw [hdim] at hbefore
  rw [hb] at hr
  omega

/-- On a positive-Euler child open the old multiplication kernel consists
exactly of Koszul boundaries. -/
theorem kernel_le_of_expected (q : Fin r → Forms K n 2) (hq : LinearIndependent K q)
    (hd : finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val))))=expectedDimension n r)
    (hchi : 0 ≤ Counts.chi n r) :
    LinearMap.ker (quadraticMultiplication q) ≤ koszulSpace q := by
  have he := quartic_euler_identity q hq
  rw [hd] at he
  change ((Counts.chi n r).toNat:ℤ)-_= _ at he
  have hhom := homology_add_pairs q hq
  have hb : finrank K (koszulSpace q)=r.choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  have heq := Submodule.eq_of_le_of_finrank_eq (kernel_contains_koszul q)
    (show finrank K (koszulSpace q)=finrank K (LinearMap.ker (quadraticMultiplication q)) by omega)
  exact heq.ge

def quadraticProduct : Forms K n 2 →ₗ[K] Forms K n 2 →ₗ[K] Forms K n 4 where
  toFun := mulQuadratic
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact add_mul a.val b.val x.val
  map_smul' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact smul_mul_assoc a b.val x.val

def withSquare (q : Fin (r+1) → Forms K n 2) :
    ((Fin r → Forms K n 2) × K) →ₗ[K] Forms K n 4 :=
  (quadraticMultiplication (prefixFamily q)).coprod
    (LinearMap.toSpanSingleton K _ (mulQuadratic (q (Fin.last r)) (q (Fin.last r))))

theorem withSquare_range (q : Fin (r+1) → Forms K n 2) :
    (withSquare q).range=(quadraticMultiplication (prefixFamily q)).range ⊔
      K ∙ (mulQuadratic (q (Fin.last r)) (q (Fin.last r))) := by
  rw [withSquare,LinearMap.range_coprod,LinearMap.range_toSpanSingleton]

theorem withSquare_polynomial (f : (ι → K) → (Fin (r+1) → Forms K n 2))
    (hf : IsPolynomialFamily f) : IsPolynomialFamily (fun a => withSquare (f a)) := by
  apply isPolynomialFamily_linearMap
  intro x
  have hpre : IsPolynomialFamily (fun a => prefixFamily (f a)) :=
    hf.linear_comp (LinearMap.funLeft K (Forms K n 2) Fin.castSucc)
  have hmap : IsPolynomialFamily (fun a => multiplicationLinear (prefixFamily (f a))) :=
    hpre.linear_comp (W := ((Fin r → Forms K n 2) →ₗ[K] Forms K n 4)) (multiplicationLinear (K := K) (n := n) (r := r))
  have hmul := hmap.linear_comp
    (LinearMap.applyₗ (R := K) (M₂ := Forms K n 4) x.1)
  have hlast := hf.linear_comp (LinearMap.proj (Fin.last r))
  have hsq := hlast.bilinear hlast quadraticProduct
  have hscale : IsPolynomialFamily (fun a => x.2 • mulQuadratic (f a (Fin.last r)) (f a (Fin.last r))) :=
    (isPolynomialFamily_const x.2).smul hsq
  simpa only [withSquare,LinearMap.coprod_apply,LinearMap.toSpanSingleton_apply,
    multiplicationLinear_apply,LinearMap.applyₗ_apply_apply] using hmul.add hscale

def Conditions (q : Fin (r+1) → Forms K n 2) : Prop :=
  LinearIndependent K q ∧ Function.Surjective (quadraticMultiplication q) ∧
  LinearMap.ker (quadraticMultiplication (prefixFamily q)) ≤ koszulSpace (prefixFamily q) ∧
  mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
    (quadraticMultiplication (prefixFamily q)).range

/-- Both adjacent child ranks and the surviving marked square hold on the
same actual coefficient open. The square condition is proved by one extra
column in the old multiplication matrix. -/
theorem principal_open [CharZero K]
    (f : (ι → K) → (Fin (r+1) → Forms K n 2))
    (hf : IsPolynomialFamily f) (hfSurj : Function.Surjective f)
    (hlow : GenericQuartic K n r) (hhigh : GenericQuartic K n (r+1))
    (hlo : 0 < Counts.chi n r) (hhi : Counts.chi n (r+1) ≤ 0) :
    ∃ D : MvPolynomial ι K,(∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → Conditions (f a) := by
  classical
  let pre := fun a => prefixFamily (f a)
  have hpre : IsPolynomialFamily pre :=
    hf.linear_comp (LinearMap.funLeft K (Forms K n 2) Fin.castSucc)
  have hpreSurj : Function.Surjective pre := by
    intro q
    obtain ⟨a,ha⟩ := hfSurj (Fin.snoc q 0)
    refine ⟨a,?_⟩
    funext i
    change (f a) i.castSucc=q i
    rw [ha,Fin.snoc_castSucc]
  obtain ⟨A,⟨a₀,ha₀⟩,hA⟩ := quartic_open pre hpre hpreSurj hlow
  obtain ⟨B,⟨b₀,hb₀⟩,hB⟩ := quartic_open f hf hfSurj hhigh
  obtain ⟨hi₀,hd₀⟩ := hA a₀ ha₀
  have hproper : quarticProducts K n (Submodule.span K (Set.range (fun i => (pre a₀ i).val))) ≠ ⊤ := by
    intro htop
    have hzero : finrank K (QuarticQuotient K n
        (Submodule.span K (Set.range (fun i => (pre a₀ i).val))))=0 := by
      change finrank K ((Forms K n 4) ⧸ quarticProducts K n _)=0
      rw [htop]
      rw [Submodule.finrank_quotient,finrank_top,Nat.sub_self]
    change _=(Counts.chi n r).toNat at hd₀
    omega
  obtain ⟨v,hv⟩ := Squares.exists_square_outside_quarticProducts _ hproper
  obtain ⟨a₁,ha₁⟩ := hfSurj (Fin.snoc (pre a₀) v)
  have hpre₁ : pre a₁=pre a₀ := by
    funext i
    change (f a₁) i.castSucc=pre a₀ i
    rw [ha₁,Fin.snoc_castSucc]
  have hsquare₁ : mulQuadratic (f a₁ (Fin.last r)) (f a₁ (Fin.last r)) ∉
      (quadraticMultiplication (pre a₁)).range := by
    rw [hpre₁,ha₁,Fin.snoc_last,range_quadraticMultiplication]
    exact hv
  obtain ⟨C,hC,hCrank⟩ := rank_polynomial_principal_open (fun a => withSquare (f a))
    (withSquare_polynomial f hf) a₁
  have hCdim : finrank K (withSquare (f a₁)).range=
      finrank K (quadraticMultiplication (pre a₀)).range+1 := by
    rw [withSquare_range,Submodule.finrank_sup_span_singleton hsquare₁]
    rw [hpre₁]
  have hA0 : A≠0 := by intro h; simp [h] at ha₀
  have hB0 : B≠0 := by intro h; simp [h] at hb₀
  have hC0 : C≠0 := by intro h; simp [h] at hC
  obtain ⟨a₂,ha₂⟩ := nonempty_principal_intersection (![A,B,C] : Fin 3 → MvPolynomial ι K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨A*B*C,⟨a₂,?_⟩,?_⟩
  · simp only [map_mul]
    exact mul_ne_zero (mul_ne_zero (ha₂ 0) (ha₂ 1)) (ha₂ 2)
  · intro a ha
    rw [map_mul,mul_ne_zero_iff,map_mul,mul_ne_zero_iff] at ha
    obtain ⟨hip,hdp⟩ := hA a ha.1.1
    obtain ⟨hi,hd⟩ := hB a ha.1.2
    have hsurj : Function.Surjective (quadraticMultiplication (f a)) := by
      apply LinearMap.range_eq_top.mp
      apply Submodule.eq_top_of_finrank_eq
      have he := quartic_quotient_add_rank (f a)
      rw [hd] at he
      change (Counts.chi n (r+1)).toNat+_=_ at he
      rw [Int.toNat_of_nonpos hhi] at he
      simpa only [zero_add,finrank_quartics] using he
    refine ⟨hi,hsurj,kernel_le_of_expected (pre a) hip hdp hlo.le,?_⟩
    intro hsquare
    have hsame : (withSquare (f a)).range=(quadraticMultiplication (pre a)).range := by
      rw [withSquare_range]
      exact sup_eq_left.mpr (Submodule.span_le.mpr (by intro v hv; rcases hv with rfl; exact hsquare))
    have hr := hCrank a ha.2
    rw [hCdim,hsame] at hr
    have hd0 := quartic_quotient_add_rank (pre a₀)
    have hda := quartic_quotient_add_rank (pre a)
    rw [hd₀] at hd0
    rw [hdp] at hda
    omega

/-- The marked coefficient map is now proved injective at the chosen flag. -/
theorem marked_injective (q : Fin (r+1) → Forms K n 2) (hq : Conditions q) :
    Function.Injective (MarkedCoefficient.markedCoefficientMap q) :=
  MarkedCoefficient.markedCoefficientMap_injective q hq.2.2.1 hq.2.2.2

/-- Its image has precisely the child defect required by the transfer. -/
theorem marked_finrank (q : Fin (r+1) → Forms K n 2) (hq : Conditions q) :
    (finrank K (MarkedCoefficient.markedCoefficientMap q).range:ℤ)=Counts.delta n (r+1) := by
  rw [LinearMap.finrank_range_of_inj (marked_injective q hq)]
  have he := quartic_euler_identity q hq.1
  have hd := quartic_quotient_add_rank q
  rw [LinearMap.range_eq_top.mpr hq.2.1,finrank_top,finrank_quartics] at hd
  change (finrank K (QuarticHomology q):ℤ)= -Counts.chi n (r+1)
  have hz : finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val))))=0 := by omega
  rw [hz] at he
  omega

/-- The marked subspace used by the response is the image of actual child
cycles, so every member automatically has an actual source representative. -/
def markedCycles (q : Fin r → Forms K n 2) (k : Fin r) :
    (quadraticMultiplication q).ker →ₗ[K]
      (Forms K n 2 ⧸ Submodule.span K (Set.range q)) :=
  MarkedCoefficient.coefficientOnCycles (quadraticMultiplication q) (LinearMap.proj k)
    (Submodule.span K (Set.range q))

theorem markedCycles_range (q : Fin (r+1) → Forms K n 2) :
    (markedCycles q (Fin.last r)).range=(MarkedCoefficient.markedCoefficientMap q).range := by
  rw [MarkedCoefficient.markedCoefficientMap,MarkedCoefficient.quotientCoefficient,
    Submodule.range_liftQ]
  rfl

def Data (q : Fin r → Forms K n 2) : Prop :=
  LinearIndependent K q ∧ Function.Surjective (quadraticMultiplication q) ∧
    ∃ k : Fin r,(finrank K (markedCycles q k).range:ℤ)=Counts.delta n r

theorem conditions_data (q : Fin (r+1) → Forms K n 2) (hq : Conditions q) : Data q := by
  refine ⟨hq.1,hq.2.1,Fin.last r,?_⟩
  rw [markedCycles_range]
  exact marked_finrank q hq

theorem upper_positive (hn : 1 ≤ n) : 0 < UniformEndpoint.upperEndpoint n := by
  by_contra! hz
  have he : UniformEndpoint.upperEndpoint n=0 := by omega
  have hu := UniformEndpoint.upper_nonpositive n
  rw [he] at hu
  have hb : 0 < (n+3).choose 4 := Nat.choose_pos (by omega)
  simp only [Counts.chi,Counts.b4,Counts.b2,Nat.cast_zero,zero_mul,sub_zero,
    Nat.choose_eq_zero_of_lt (by omega : 0 < 2),add_zero] at hu
  omega

/-- The induction premise supplies one actual upper-child flag on a nonempty
open in any surjective polynomial parameter family. This includes integral
Euler roots: the predecessor still has strictly positive Euler count. -/
theorem endpoint_principal_open [CharZero K] (hn : 1 ≤ n) (q : ℕ)
    (hq : q=UniformEndpoint.upperEndpoint n)
    (f : (ι → K) → (Fin q → Forms K n 2))
    (hf : IsPolynomialFamily f) (hfSurj : Function.Surjective f)
    (hchild : ∀ r,r ≤ (n+1).choose 2 → GenericQuartic K n r) :
    ∃ D : MvPolynomial ι K,(∃ a,eval a D≠0) ∧
      ∀ a,eval a D≠0 → Data (f a) := by
  cases q with
  | zero => have hpos := upper_positive hn; omega
  | succ r =>
    have hlo := UniformEndpoint.before_upper_positive n r (by omega)
    have hhi : Counts.chi n (r+1) ≤ 0 := by rw [hq]; exact UniformEndpoint.upper_nonpositive n
    have hle := UniformEndpoint.upper_le_quadratics n
    obtain ⟨D,hD,hgood⟩ := principal_open f hf hfSurj
      (hchild r (by omega)) (hchild (r+1) (by omega)) hlo hhi
    exact ⟨D,hD,fun a ha => conditions_data (f a) (hgood a ha)⟩

end Quartic.SharedChildFlag
