import Quartic.SmallCovectorCommonOpen
import Quartic.SliceMotionAvoidance

/-! Motion avoidance on the actual common small-range coefficient locus. -/
noncomputable section
namespace Quartic.SmallCovectorMotion
open Module MvPolynomial Matrix KernelPolynomialCharts UniformEndpoint ProfileCertificate
open SmallCovectorCommonOpen RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts
variable {K : Type*} [Field K]
variable {m : ℕ} {upper : Bool} {a₁ a₂ n₁ n₂ r₁ r₂ : ℕ}

abbrev Parameters (K : Type*) [Field K] (m : ℕ) (upper : Bool) :=
  ParameterIndex m upper m (mixedCount m upper) (upperEndpoint m) → K

def mixed (p : Parameters K m upper) : Fin (mixedCount m upper) → Fin (RowCount m 1) → K :=
  fun j => rowFiniteEquiv (AugmentedGeneric.coefficientMixed (baseProjection p) j)
def child (p : Parameters K m upper) : Fin (upperEndpoint m) → Fin (FormCount m 2) → K :=
  fun i => finiteEquiv (AugmentedGeneric.coefficientChild (baseProjection p) i)
def slices (p : Parameters K m upper) (d : Threshold m upper) :
    Fin (ConvolutionClosedSlices.sliceCount m upper d.val) → Fin (RowCount m 3) → K :=
  fun j => rowFiniteEquiv (coefficientSlices p d j)

include K in
theorem threshold_le_ambient (hm : 28 ≤ m) (d : Threshold m upper) :
    d.val+mixedCount m upper ≤ RowCount m 1 := by
  rw [rowCount_one (K := K)]
  have hc := ConvolutionAllRange.endpoint_columns_range m hm upper
  have he := totalA_eq m _ hc.1 hc.2
  have hd := d.isLt
  omega

/-- The E-annihilation equations imply the lower endpoint c for the ambient kernel. -/
theorem kernel_lower (p : Parameters K m upper)
    (hg : LinearIndependent K (AugmentedGeneric.coefficientMixed (baseProjection p)))
    (ell : Fin (RowCount m 3) → K)
    (hE : ∀ j f,covector ell (coordinate f (mixed p j))=0) :
    mixedCount m upper ≤ finrank K (LinearMap.ker (relationMap coordinate ell)) := by
  have hcoord : LinearIndependent K (mixed p) := hg.map' rowFiniteEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr rowFiniteEquiv.injective)
  have hle : Submodule.span K (Set.range (mixed p)) ≤
      LinearMap.ker (relationMap coordinate ell) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (AmbientCovectorTransport.mem_relationMap_ker_iff coordinate ell (mixed p j)).mpr (hE j)
  have h := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hcoord,Fintype.card_fin] at h

/-- The original homogeneous equations are precisely the ambient minors and
E/Q products; all auxiliary equations are separate linear slices. -/
theorem empty_section (hm : 28 ≤ m) (p : Parameters K m upper) (hp : ClosedConditions p)
    (d : Threshold m upper) :
    ∀ ell : Fin (RowCount m 3) → K,
      (∀ j,aeval ell (AmbientCovectorSpreading.finiteOriginalEquations (d := d.val)
        coordinate (mixed p) (child p) j).val=0) →
      (∀ j,aeval ell (AmbientCovectorSpreading.slices (slices p d) j).val=0) → ell=0 := by
  intro ell hf hZ
  have h := (AmbientCovectorSpreading.finite_original_equations_iff coordinate
    (mixed p) (child p) (threshold_le_ambient (K := K) hm d) ell).mp
      (by simpa only [aeval_eq_eval] using hf)
  apply hp d ell h.1 h.2.1 h.2.2
  intro j
  simpa only [aeval_eq_eval,AmbientCovectorSpreading.slices,
    ClosedCovectorEquations.eval_linearForm,slices] using hZ j

/-- At a point of the proved common open, the projective motion theorem
applies to the literal ambient equations. -/
theorem principal_open_two_stage [IsAlgClosed K] (hm : 28 ≤ m) (p : Parameters K m upper)
    (hp : ClosedConditions p) (d : Threshold m upper)
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin (RowCount m 3)) K))
    (B : Matrix (Fin a₂) (Fin n₂) (MvPolynomial (Fin (RowCount m 3) ⊕ Fin n₁) K))
    (hA : ∀ (s : K) ell,evaluated A (s • ell)=s • evaluated A ell)
    (hB : ∀ (s : K) ell x,evaluated B (Sum.elim (s • ell) x)=s • evaluated B (Sum.elim ell x))
    (hcount : ConvolutionClosedSlices.sliceCount m upper d.val ≤ r₁+r₂) :
    ∃ P : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
      (∃ z,eval z P ≠ 0) ∧ ∀ z,eval z P ≠ 0 →
        ∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
          d.val+mixedCount m upper ≤ finrank K (LinearMap.ker (relationMap coordinate ell)) →
          (∀ j f,covector ell (coordinate f (mixed p j))=0) →
          (∀ i v,covector ell (coordinate (child p i) v)=0) →
          r₁ ≤ (evaluated A ell).rank →
          r₂ ≤ (evaluated B (Sum.elim ell (fun i => z (Sum.inl i)))).rank →
          evaluated A ell *ᵥ (fun i => z (Sum.inl i)) ≠ 0 ∨
            evaluated B (Sum.elim ell (fun i => z (Sum.inl i))) *ᵥ (fun j => z (Sum.inr j)) ≠ 0 := by
  obtain ⟨P,hP,hgood⟩ := SliceMotionAvoidance.principal_open_projective (L := K)
    (AmbientCovectorSpreading.finiteDegree (RowCount m 1) (FormCount m 2)
      (mixedCount m upper) (upperEndpoint m) d.val)
    (AmbientCovectorSpreading.finiteOriginalEquations coordinate (mixed p) (child p))
    (AmbientCovectorSpreading.slices (slices p d)) (empty_section hm p hp d) A B hA hB hcount
  refine ⟨P,hP,?_⟩
  intro z hz ell hell hker hE hQ
  apply hgood z hz ell hell
  exact (AmbientCovectorSpreading.finite_original_equations_iff coordinate (mixed p) (child p)
    (threshold_le_ambient (K := K) hm d) ell).mpr ⟨hker,hE,hQ⟩

/-- Taking the finite product over the true quotient kernel dimensions
removes rank premises from the conclusion on the actual Good locus. -/
theorem principal_open_all_kernel_ranks [IsAlgClosed K] (hm : 28 ≤ m)
    (p : Parameters K m upper) (hp : ClosedConditions p)
    (hg : LinearIndependent K (AugmentedGeneric.coefficientMixed (baseProjection p)))
    (A : Matrix (Fin a₁) (Fin n₁) (MvPolynomial (Fin (RowCount m 3)) K))
    (B : Matrix (Fin a₂) (Fin n₂) (MvPolynomial (Fin (RowCount m 3) ⊕ Fin n₁) K))
    (hA : ∀ (s : K) ell,evaluated A (s • ell)=s • evaluated A ell)
    (hB : ∀ (s : K) ell x,evaluated B (Sum.elim (s • ell) x)=s • evaluated B (Sum.elim ell x))
    (r₁ r₂ : Threshold m upper → ℕ)
    (hcount : ∀ d,ConvolutionClosedSlices.sliceCount m upper d.val ≤ r₁ d+r₂ d)
    (Good : (Fin n₁ ⊕ Fin n₂ → K) → Prop)
    (hr₁ : ∀ d : Threshold m upper,∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
      (∀ j f,covector ell (coordinate f (mixed p j))=0) →
      (∀ i v,covector ell (coordinate (child p i) v)=0) →
      finrank K (LinearMap.ker (relationMap coordinate ell))=d.val+mixedCount m upper →
      ∀ z,Good z → r₁ d ≤ (evaluated A ell).rank)
    (hr₂ : ∀ d : Threshold m upper,∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
      (∀ j f,covector ell (coordinate f (mixed p j))=0) →
      (∀ i v,covector ell (coordinate (child p i) v)=0) →
      finrank K (LinearMap.ker (relationMap coordinate ell))=d.val+mixedCount m upper →
      ∀ z,Good z → evaluated A ell *ᵥ (fun i => z (Sum.inl i))=0 →
        r₂ d ≤ (evaluated B (Sum.elim ell (fun i => z (Sum.inl i)))).rank) :
    ∃ P : MvPolynomial (Fin n₁ ⊕ Fin n₂) K,
      (∃ z,eval z P ≠ 0) ∧ ∀ z,eval z P ≠ 0 → Good z →
        ∀ ell : Fin (RowCount m 3) → K,ell ≠ 0 →
          (∀ j f,covector ell (coordinate f (mixed p j))=0) →
          (∀ i v,covector ell (coordinate (child p i) v)=0) →
          evaluated A ell *ᵥ (fun i => z (Sum.inl i)) ≠ 0 ∨
            evaluated B (Sum.elim ell (fun i => z (Sum.inl i))) *ᵥ (fun j => z (Sum.inr j)) ≠ 0 := by
  classical
  choose P hP hgood using fun d : Threshold m upper =>
    principal_open_two_stage hm p hp d A B hA hB (hcount d)
  have hPnz (d : Threshold m upper) : P d ≠ 0 := by
    obtain ⟨z,hz⟩ := hP d
    intro h
    exact hz (by rw [h,map_zero])
  refine ⟨∏ d,P d,PolynomialImageAvoidance.exists_eval_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun d _ => hPnz d)),?_⟩
  intro z hz hGood ell hell hE hQ
  by_contra! hbad
  have hc := kernel_lower p hg ell hE
  have hdim : finrank K (LinearMap.ker (relationMap coordinate ell)) ≤ RowCount m 1 := by
    simpa only [Module.finrank_fin_fun] using
      (LinearMap.ker (relationMap (coordinate (K := K) (m := m)) ell)).finrank_le
  have hbounds := ConvolutionAllRange.endpoint_columns_range m hm upper
  have htotal := totalA_eq m _ hbounds.1 hbounds.2
  have hambient : RowCount m 1 = 3*m := rowCount_one (K := K) m
  let d : Threshold m upper :=
    ⟨finrank K (LinearMap.ker (relationMap coordinate ell))-mixedCount m upper,by omega⟩
  have hd : finrank K (LinearMap.ker (relationMap coordinate ell))=d.val+mixedCount m upper := by
    dsimp [d]
    omega
  have hz' : eval z (P d) ≠ 0 := by
    rw [map_prod] at hz
    exact Finset.prod_ne_zero_iff.mp hz d (Finset.mem_univ d)
  have h := hgood d z hz' ell hell hd.ge hE hQ (hr₁ d ell hell hE hQ hd z hGood)
    (hr₂ d ell hell hE hQ hd z hGood hbad.1)
  exact h.elim (fun h => h hbad.1) (fun h => h hbad.2)

/-- Fixing actual g and h leaves a nonempty determinant open of pure motions
satisfying the augmented Good condition, whenever one such motion is known. -/
theorem augmented_motion_open {m c q N : ℕ}
    (g : Fin c → MiddleCoordinates.Mixed K m) (h : Fin q → Forms K m 2)
    (e : (Fin 4 → Forms K m 2) ≃ₗ[K] (Fin N → K))
    (r₀ : Fin 4 → Forms K m 2) (hh : LinearIndependent K h)
    (hr₀ : Function.Injective
      (AugmentedGeneric.quotientAugmented (AugmentedGeneric.productMap g) h r₀)) :
    ∃ D : MvPolynomial (Fin N) K,eval (e r₀) D ≠ 0 ∧ ∀ x,eval x D ≠ 0 →
      Function.Injective (AugmentedGeneric.quotientAugmented
        (AugmentedGeneric.productMap g) h (e.symm x)) := by
  classical
  have hpoly := AugmentedGeneric.lifted_polynomial
    (fun _ : Fin N → K => AugmentedGeneric.productMap g)
    (fun _ : Fin N → K => h) (fun x : Fin N → K => e.symm x)
    (isPolynomialFamily_const _) (fun _ => isPolynomialFamily_const _)
    (fun i => isPolynomialFamily_linear ((LinearMap.proj i).comp e.symm.toLinearMap))
  have hw : Function.Injective (AugmentedGeneric.lifted (AugmentedGeneric.productMap g)
      h (e.symm (e r₀))) := by
    rw [LinearEquiv.symm_apply_apply]
    exact AugmentedGeneric.lifted_injective_of_quotient _ _ _ hh hr₀
  obtain ⟨D,hD,hgood⟩ := injective_polynomial_principal_open
    (fun x : Fin N → K => AugmentedGeneric.lifted (AugmentedGeneric.productMap g) h (e.symm x))
    hpoly (e r₀) hw
  exact ⟨D,hD,fun x hx => AugmentedGeneric.quotient_injective_of_lifted _ _ _ (hgood x hx)⟩

/-- The target surplus supplies exactly the auxiliary conditions needed by
the two clipped motion ranks, including every zero-rank boundary. -/
theorem slice_budget (j : ℤ) (k h c d : ℕ) :
    (j-((c:ℤ)+4)*(d:ℤ)).toNat ≤ (k-4*d)+(h-c*d)+(j-((k:ℤ)+h)).toNat := by
  have h1 := Int.self_le_toNat ((k:ℤ)-4*d)
  have h2 := Int.self_le_toNat ((h:ℤ)-c*d)
  have h3 := Int.self_le_toNat (j-((k:ℤ)+h))
  have he1 : ((k:ℤ)-4*d).toNat = k-4*d := by omega
  have he2 : ((h:ℤ)-c*d).toNat = h-c*d := by omega
  rw [he1] at h1
  rw [he2] at h2
  apply Int.toNat_le.mpr
  push_cast
  nlinarith

end Quartic.SmallCovectorMotion
