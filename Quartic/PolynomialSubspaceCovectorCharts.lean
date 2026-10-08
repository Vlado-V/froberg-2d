import Quartic.BilinearCoefficientKernel
import Quartic.SharedKernelAvoidance
import Quartic.PolynomialRankOpen

/-!
# Covector incidence from arbitrary polynomial subspace charts

The input vectors have literal polynomial coordinates. Their actual span is
the charted subspace; no independence or image-rank assertion is implicit.
Projective kernel charts give the count g+T-e-1, and shared kernel avoidance
excludes the corresponding negative conditioned strata.
-/

noncomputable section
namespace Quartic.PolynomialSubspaceCovectorCharts
set_option maxHeartbeats 1000000
open Module Matrix MvPolynomial SubspaceCharts KernelPolynomialCharts
open BilinearCovectorCharts (covector covector_apply)
open BilinearCoefficientKernel
variable {K I : Type*} [Field K] {a b T N e : ℕ}

/-- An actual evaluated polynomial vector. -/
def vector (H : Fin N → Fin a → MvPolynomial I K) (t : I → K) (i : Fin N) : Fin a → K :=
  fun k => eval t (H i k)

/-- The subspace actually spanned by a polynomial chart. -/
def subspace (H : Fin N → Fin a → MvPolynomial I K) (t : I → K) : Submodule K (Fin a → K) :=
  Submodule.span K (Set.range (vector H t))

/-- The covector equations imposed by products with the actual chart vectors. -/
def constraint (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) :
    Matrix (Fin (N*b)) (Fin T) (MvPolynomial I K) :=
  fun l k => ∑ h : Fin a,H (finProdFinEquiv.symm l).1 h *
    C (mu (Pi.single (finProdFinEquiv.symm l).2 1) (Pi.single h 1) k)

theorem eval_constraint (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (t : I → K) (l : Fin (N*b)) (k : Fin T) :
    evaluated (constraint mu H) t l k=
      mu (Pi.single (finProdFinEquiv.symm l).2 1) (vector H t (finProdFinEquiv.symm l).1) k := by
  classical
  change eval t (constraint mu H l k)=_
  conv_rhs => rw [← (Pi.basisFun K (Fin a)).sum_equivFun (vector H t (finProdFinEquiv.symm l).1)]
  simp [constraint,vector,Pi.basisFun_apply,Pi.basisFun_equivFun,map_sum,map_smul,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

/-- Constraint rank equals the actual bilinear-image dimension of the spanned subspace. -/
theorem constraint_rank (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (t : I → K) :
    (evaluated (constraint mu H) t).rank=finrank K (BilinearImage.image mu (subspace H t)) := by
  classical
  rw [← Matrix.rank_transpose,Matrix.rank_eq_finrank_span_cols,subspace,
    BilinearImage.image_span_basis (Pi.basisFun K (Fin b))]
  have hset : Set.range (evaluated (constraint mu H) t).transpose.col=
      Set.range (fun z : Fin N × Fin b => mu ((Pi.basisFun K (Fin b)) z.2) (vector H t z.1)) := by
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      refine ⟨finProdFinEquiv.symm l,?_⟩
      funext k
      simpa only [Matrix.col_apply,Matrix.transpose_apply,Pi.basisFun_apply] using
        (eval_constraint mu H t l k).symm
    · rintro ⟨⟨i,h⟩,rfl⟩
      refine ⟨finProdFinEquiv (i,h),?_⟩
      funext k
      simpa only [Equiv.symm_apply_apply,Pi.basisFun_apply,Matrix.col_apply,Matrix.transpose_apply] using
        eval_constraint mu H t (finProdFinEquiv (i,h)) k
  rw [hset]

theorem constraint_mulVec (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (t : I → K) (ell : Fin T → K) (l : Fin (N*b)) :
    (evaluated (constraint mu H) t *ᵥ ell) l=covector ell
      (mu (Pi.single (finProdFinEquiv.symm l).2 1) (vector H t (finProdFinEquiv.symm l).1)) := by
  simp only [Matrix.mulVec,dotProduct,eval_constraint,covector_apply,mul_comm]

/-- The matrix kernel is exactly the annihilator of the actual product image. -/
theorem constraint_kernel_iff (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (t : I → K) (ell : Fin T → K) :
    evaluated (constraint mu H) t *ᵥ ell=0 ↔
      BilinearImage.image mu (subspace H t) ≤ LinearMap.ker (covector ell) := by
  classical
  rw [subspace,BilinearImage.image_span_basis (Pi.basisFun K (Fin b))]
  constructor
  · intro hz
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,h⟩,rfl⟩
    change covector ell (mu ((Pi.basisFun K (Fin b)) h) (vector H t i))=0
    have he := congrFun hz (finProdFinEquiv (i,h))
    rw [constraint_mulVec] at he
    simpa only [Equiv.symm_apply_apply,Pi.zero_apply,Pi.basisFun_apply] using he
  · intro h
    funext l
    rw [constraint_mulVec]
    exact h (Submodule.subset_span ⟨finProdFinEquiv.symm l,by simp only [Pi.basisFun_apply]⟩)

/-- Minor choices and a nonzero free coordinate of the covector. -/
abbrev ChartType (b T N e : ℕ) :=
  (Fin e ↪ Fin (N*b)) × (v : Fin e ↪ Fin T) × Outside v

abbrev Parameters (I : Type*) (c : ChartType b T N e) :=
  ProjectiveKernelCharts.Parameters I c.2.1 c.2.2

def numerator (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (c : ChartType b T N e) :
    Fin T → MvPolynomial (Parameters I c) K :=
  ProjectiveKernelCharts.numerator (constraint mu H) c.1 c.2.1 c.2.2

def denominator (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (c : ChartType b T N e) :
    MvPolynomial (Parameters I c) K :=
  ProjectiveKernelCharts.denominator (constraint mu H) c.1 c.2.1 c.2.2

theorem parameter_count [Fintype I] (c : ChartType b T N e) :
    Fintype.card (Parameters I c)=Fintype.card I+(T-e)-1 :=
  ProjectiveKernelCharts.parameter_count c.2.1 c.2.2

/-- Every actual nonzero annihilator is covered projectively, preserving all
original subspace parameters inside the same rational chart. -/
theorem cover_annihilator (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : Fin N → Fin a → MvPolynomial I K) (t : I → K)
    (himage : e ≤ finrank K (BilinearImage.image mu (subspace H t)))
    (ell : Fin T → K) (hnz : ell ≠ 0)
    (hann : BilinearImage.image mu (subspace H t) ≤ LinearMap.ker (covector ell)) :
    ∃ c : ChartType b T N e,∃ p : Parameters I c → K,∃ s : K,
      s ≠ 0 ∧ (∀ i,p (Sum.inl i)=t i) ∧ eval p (denominator mu H c) ≠ 0 ∧
        ell=s • RationalImageAvoidance.rationalMap (numerator mu H c) (denominator mu H c) p := by
  classical
  have hrank : e ≤ (evaluated (constraint mu H) t).rank := by rwa [constraint_rank]
  obtain ⟨u,v,hdet⟩ := KernelCharts.exists_minor_of_rank_le (evaluated (constraint mu H) t) hrank
  have hker : evaluated (constraint mu H) t *ᵥ ell=0 := (constraint_kernel_iff mu H t ell).mpr hann
  obtain ⟨z,p,s,hs,hp,hden,he⟩ :=
    ProjectiveKernelCharts.cover_nonzero_kernel (constraint mu H) u v t hdet ell hker hnz
  exact ⟨⟨u,v,z⟩,p,s,hs,hp,hden,he⟩

/-- A subspace annihilated by a nonzero coordinate covector is strictly
smaller than the full target, over every field. -/
theorem annihilated_finrank_lt (S : Submodule K (Fin T → K))
    (ell : Fin T → K) (hnz : ell ≠ 0) (hann : S ≤ LinearMap.ker (covector ell)) :
    finrank K S < T := by
  classical
  by_contra h
  have hle : finrank K S ≤ T := by simpa using S.finrank_le
  have he : finrank K S=T := by omega
  have htop : S=⊤ := Submodule.eq_top_of_finrank_eq (by simpa using he)
  apply hnz
  funext k
  have hz := hann (show Pi.single k (1 : K) ∈ S from by simp [htop])
  change covector ell (Pi.single k 1)=0 at hz
  simpa [covector_apply,Pi.single_apply] using hz

/-- In particular, a nonzero annihilator forces every actual bilinear image
it annihilates to have dimension strictly below the target dimension. -/
theorem image_finrank_lt (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (S : Submodule K (Fin a → K)) (ell : Fin T → K) (hnz : ell ≠ 0)
    (hann : BilinearImage.image mu S ≤ LinearMap.ker (covector ell)) :
    finrank K (BilinearImage.image mu S) < T :=
  annihilated_finrank_lt _ ell hnz hann

section FiniteFamily
variable {C : Type*} [Fintype C] {I : C → Type*} [∀ c,Fintype (I c)] {d q : ℕ}

/-- Coverage by the supplied literal polynomial chart vectors. -/
def Covered (H : ∀ c,Fin N → Fin a → MvPolynomial (I c) K)
    (S : Submodule K (Fin a → K)) : Prop :=
  ∃ c,∃ t : I c → K,subspace (H c) t=S

/-- A negative projective parameter count excludes the entire covered
kernel-dimension stratum for one shared tuple of coefficient vectors. -/
theorem principal_open_excludes_covered_stratum [Infinite K]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : ∀ c,Fin N → Fin a → MvPolynomial (I c) K)
    (hcount : ∀ c,Fintype.card (I c)+(T-e)-1 < q*(a-d)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      (∃ Q : Fin q × Fin b → K,eval Q P ≠ 0) ∧
      ∀ Q,eval Q P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        finrank K (LinearMap.ker (relationMap mu ell))=d →
        Covered H (LinearMap.ker (relationMap mu ell)) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ∃ i : Fin q,∃ v : Fin a → K,covector ell (mu (fun k => Q (i,k)) v) ≠ 0 := by
  classical
  let Choices := C × ChartType b T N e
  let A (c : Choices) := polynomialMatrix mu (numerator mu (H c.1) c.2)
  have hchart (c : Choices) :
      ∃ P : MvPolynomial (Fin q × Fin b) K,
        (∃ Q : Fin q × Fin b → K,eval Q P ≠ 0) ∧
        ∀ Q,eval Q P ≠ 0 → ∀ p : Parameters (I c.1) c.2 → K,
          a-d ≤ (evaluated (A c) p).rank →
          ∃ i : Fin q,evaluated (A c) p *ᵥ (fun k => Q (i,k)) ≠ 0 := by
    apply SharedKernelAvoidance.principal_open_avoids_shared_kernels (A c)
    rw [parameter_count]
    exact hcount c.1
  choose P hP hgood using hchart
  have hne (c : Choices) : P c ≠ 0 := by
    obtain ⟨Q,hQ⟩ := hP c
    intro hz
    simp [hz] at hQ
  obtain ⟨Q₀,hQ₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ c,P c,⟨Q₀,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun c _ => hQ₀ c)
  intro Q hQ ell hell hdim hcover himage
  by_contra! hann
  obtain ⟨c,t,ht⟩ := hcover
  obtain ⟨k,p,s,hs,_,hden,hscale⟩ := cover_annihilator (e := e) mu (H c) t
    (by rw [ht]; exact himage) ell hell (by rw [ht]; exact kernel_image_annihilated mu ell)
  let ell' := RationalImageAvoidance.rationalMap (numerator mu (H c) k) (denominator mu (H c) k) p
  have hscale' : ell=s • ell' := hscale
  have hrank : (coefficientMatrix mu ell').rank=a-d := by
    have h := coefficientMatrix_rank_of_kernel_finrank mu ell d hdim
    rw [hscale',coefficientMatrix_rank_smul mu s hs] at h
    exact h
  have hnum : (fun h => eval p (numerator mu (H c) k h))=
      eval p (denominator mu (H c) k) • ell' := by
    funext h
    change eval p (numerator mu (H c) k h)=eval p (denominator mu (H c) k)*
      (eval p (numerator mu (H c) k h)/eval p (denominator mu (H c) k))
    field_simp
  have hArank : a-d ≤ (evaluated (A (c,k)) p).rank := by
    change a-d ≤ (evaluated (polynomialMatrix mu (numerator mu (H c) k)) p).rank
    rw [evaluated_polynomialMatrix,hnum,coefficientMatrix_rank_smul mu _ hden,hrank]
  have hQp : eval Q (P (c,k)) ≠ 0 := by
    have hall : ∀ c,eval Q (P c) ≠ 0 := by
      simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hQ
    exact hall (c,k)
  obtain ⟨i,hi⟩ := hgood (c,k) Q hQp p hArank
  apply hi
  change evaluated (polynomialMatrix mu (numerator mu (H c) k)) p *ᵥ (fun h => Q (i,h))=0
  rw [evaluated_polynomialMatrix,hnum,coefficientMatrix_kernel_iff]
  intro v
  rw [covector_smul,LinearMap.smul_apply]
  have h := hann i v
  rw [hscale',covector_smul,LinearMap.smul_apply] at h
  have hz := (smul_eq_zero.mp h).resolve_left hs
  rw [hz,smul_zero]

/-- A uniform upper bound g on scalar chart parameters gives the expected
negative conditioned count g+T-e-1-q(a-d). -/
theorem principal_open_excludes_covered_stratum_of_bound [Infinite K]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : ∀ c,Fin N → Fin a → MvPolynomial (I c) K) (g : ℕ)
    (hg : ∀ c,Fintype.card (I c) ≤ g) (hcount : g+(T-e)-1 < q*(a-d)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      (∃ Q : Fin q × Fin b → K,eval Q P ≠ 0) ∧
      ∀ Q,eval Q P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        finrank K (LinearMap.ker (relationMap mu ell))=d →
        Covered H (LinearMap.ker (relationMap mu ell)) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ∃ i : Fin q,∃ v : Fin a → K,covector ell (mu (fun k => Q (i,k)) v) ≠ 0 := by
  apply principal_open_excludes_covered_stratum mu H
  intro c
  have hc := hg c
  omega

/-- Integer-valued parameter bounds are accepted directly, including the
empty full-image case e≥T. No truncated projective dimension is interpreted
as a nonempty covector family. -/
theorem principal_open_excludes_covered_stratum_of_int_bound [Infinite K]
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (H : ∀ c,Fin N → Fin a → MvPolynomial (I c) K) (g : ℤ)
    (hg : ∀ c,(Fintype.card (I c):ℤ) ≤ g)
    (hcount : g+(T:ℤ)-(e:ℤ)-1 < (q*(a-d):ℕ)) :
    ∃ P : MvPolynomial (Fin q × Fin b) K,
      (∃ Q : Fin q × Fin b → K,eval Q P ≠ 0) ∧
      ∀ Q,eval Q P ≠ 0 → ∀ ell : Fin T → K,ell ≠ 0 →
        finrank K (LinearMap.ker (relationMap mu ell))=d →
        Covered H (LinearMap.ker (relationMap mu ell)) →
        e ≤ finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) →
        ∃ i : Fin q,∃ v : Fin a → K,covector ell (mu (fun k => Q (i,k)) v) ≠ 0 := by
  classical
  by_cases he:e < T
  · apply principal_open_excludes_covered_stratum (e := e) mu H
    intro c
    have hc := hg c
    omega
  · refine ⟨1,⟨0,by simp⟩,?_⟩
    intro Q _ ell hell _ hcover himage
    obtain ⟨c,t,ht⟩ := hcover
    obtain ⟨k,p,s,hs,hp,hden,hscale⟩ := cover_annihilator (e := e) mu (H c) t
      (by rw [ht]; exact himage) ell hell (by rw [ht]; exact kernel_image_annihilated mu ell)
    have hpos : 0 < Fintype.card (Outside k.2.1) := Fintype.card_pos_iff.mpr ⟨k.2.2⟩
    rw [card_outside] at hpos
    omega

end FiniteFamily

end Quartic.PolynomialSubspaceCovectorCharts
