module

public import Quartic.SharedCovectorPolynomial
public import Quartic.PolynomialSubspaceCovectorCharts

@[expose] public section

/-!
# Empty sliced covector strata from actual polynomial charts

The auxiliary target vectors impose homogeneous linear slices on the same
covector. Their contribution is proved by the actual simultaneous constraint
matrix. The conclusion excludes nonzero covectors; no positive fiber dimension
is inferred. Over an algebraically closed field it is geometric emptiness.
-/
noncomputable section
namespace Quartic.SlicedCovectorAvoidance
open Module Matrix MvPolynomial KernelPolynomialCharts PolynomialBilinearCoordinates
open BilinearCoefficientKernel BilinearCovectorCharts
open PolynomialSubspaceCovectorCharts
variable {K C : Type*} [Field K] [Infinite K] [Fintype C]
variable {I : C → Type*} [∀ c,Fintype (I c)] {a b T N d e q s : ℕ}

/-- A nonempty joint coefficient/slice open excludes the entire covered
covector stratum whenever its projective count is strictly smaller than the
actual shared-coefficient and slice rank. -/
theorem principal_open_excludes_sliced_stratum
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : ∀ c,Fin N → Fin a → MvPolynomial (I c) K)
    (hcount : ∀ c,Fintype.card (I c)+(T-e)-1 < q*(a-d)+s) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ x : SharedCovectorPolynomial.Input K b T q s,
        eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,ell ≠ 0 →
        finrank K (LinearMap.ker (relationMap mu ell))=d →
        Covered H (LinearMap.ker (relationMap mu ell)) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ¬((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
  classical
  let Choices := C × ChartType b T N e
  let A (c : Choices) := SharedCovectorPolynomial.polynomialMatrix (q := q) (e := s)
    mu (numerator mu (H c.1) c.2)
  have hchart (c : Choices) :
      ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
        (∃ z,eval z P ≠ 0) ∧ ∀ z,eval z P ≠ 0 →
          ∀ p : Parameters (I c.1) c.2 → K,
          q*(a-d)+s ≤ (evaluated (A c) p).rank → evaluated (A c) p *ᵥ z ≠ 0 := by
    apply PolynomialKernelAvoidance.principal_open_avoids_kernels (A c)
    rw [PolynomialSubspaceCovectorCharts.parameter_count]
    exact hcount c.1
  choose P hP hgood using hchart
  have hne (c : Choices) : P c ≠ 0 := by
    obtain ⟨z,hz⟩ := hP c
    intro h
    simp [h] at hz
  obtain ⟨z₀,hz₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ c,P c,⟨(coordinates K _).symm z₀,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply,map_prod] using
      Finset.prod_ne_zero_iff.mpr (fun c _ => hz₀ c)
  intro x hx ell hell hdim hcover himage hann
  obtain ⟨c,t,ht⟩ := hcover
  obtain ⟨k,p,u,hu,_,hden,hscale⟩ := cover_annihilator (e := e) mu (H c) t
    (by rw [ht]; exact himage) ell hell (by rw [ht]; exact kernel_image_annihilated mu ell)
  let ell' := RationalImageAvoidance.rationalMap (numerator mu (H c) k) (denominator mu (H c) k) p
  have hscale' : ell=u • ell' := hscale
  have hell' : ell' ≠ 0 := by
    intro h
    rw [h,smul_zero] at hscale'
    exact hell hscale'
  have hnum : (fun h => eval p (numerator mu (H c) k h))=
      eval p (denominator mu (H c) k) • ell' := by
    funext h
    change eval p (numerator mu (H c) k h)=eval p (denominator mu (H c) k)*
      (eval p (numerator mu (H c) k h)/eval p (denominator mu (H c) k))
    field_simp
  have hnz : (fun h => eval p (numerator mu (H c) k h)) ≠ 0 := by
    rw [hnum]
    exact smul_ne_zero hden hell'
  have hdim' : finrank K (LinearMap.ker (relationMap mu
      (fun h => eval p (numerator mu (H c) k h))))=d := by
    rw [hnum,relationMap_kernel_smul mu _ hden]
    rw [hscale',relationMap_kernel_smul mu _ hu] at hdim
    exact hdim
  have hrank : q*(a-d)+s ≤ (evaluated (A (c,k)) p).rank := by
    rw [SharedCovectorPolynomial.polynomialMatrix_rank mu _ p hnz,hdim']
  have hxP : eval (coordinates K _ x) (P (c,k)) ≠ 0 := by
    have hall : ∀ c,eval (coordinates K _ x) (P c) ≠ 0 := by
      simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hx
    exact hall (c,k)
  apply hgood (c,k) _ hxP p hrank
  apply (SharedCovectorPolynomial.polynomialMatrix_kernel_iff mu _ p x).mpr
  have hvanish (v : Fin T → K) (hv : covector ell v=0) :
      covector (fun h => eval p (numerator mu (H c) k h)) v=0 := by
    rw [hnum,covector_smul,LinearMap.smul_apply]
    rw [hscale',covector_smul,LinearMap.smul_apply] at hv
    rw [(smul_eq_zero.mp hv).resolve_left hu,smul_zero]
  exact ⟨fun i v => hvanish _ (hann.1 i v),fun j => hvanish _ (hann.2 j)⟩

/-- A compressed integer parameter bound may be used directly. The case of
full image rank is empty because the covector is nonzero. -/
theorem principal_open_excludes_sliced_stratum_of_int_bound
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : ∀ c,Fin N → Fin a → MvPolynomial (I c) K) (g : ℤ)
    (hg : ∀ c,(Fintype.card (I c):ℤ) ≤ g)
    (hcount : g+(T:ℤ)-(e:ℤ)-1 < (q*(a-d)+s:ℕ)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,ell ≠ 0 →
        finrank K (LinearMap.ker (relationMap mu ell))=d →
        Covered H (LinearMap.ker (relationMap mu ell)) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ¬((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
  by_cases he : e<T
  · apply principal_open_excludes_sliced_stratum (e := e) mu H
    intro c
    have h := hg c
    omega
  · refine ⟨1,⟨0,by simp⟩,?_⟩
    intro x hx ell hell hdim hcover himage
    have hlt := image_finrank_lt mu (LinearMap.ker (relationMap mu ell)) ell hell
      (kernel_image_annihilated mu ell)
    omega

end Quartic.SlicedCovectorAvoidance
