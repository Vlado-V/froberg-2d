module

public import Quartic.ConvolutionClosedSlices
public import Quartic.ConvolutionSharedSlices
public import Quartic.ScalarJointCount

@[expose] public section

/-! Closed sliced covector loci from actual ordinary Grassmann charts. -/
noncomputable section
namespace Quartic.ExpansionClosedSlices
open Module MvPolynomial PolynomialBilinearCoordinates
open BilinearCovectorCharts BilinearCoefficientKernel
variable {K : Type*} [Field K] [Infinite K] {a b T q s : ℕ}
set_option maxHeartbeats 1500000

omit [Infinite K] in
theorem graph_covered {d : ℕ} (S : Submodule K (Fin a → K)) (hd : finrank K S=d) :
    PolynomialSubspaceCovectorCharts.Covered
      (fun j : Fin d ↪ Fin a => BilinearCovectorCharts.graphPolynomial j) S := by
  obtain ⟨j,p,hp⟩ := SubspaceCharts.exists_chart S hd
  refine ⟨j,fun z => p z.1 z.2,?_⟩
  have hv : PolynomialSubspaceCovectorCharts.vector (BilinearCovectorCharts.graphPolynomial j)
      (fun z => p z.1 z.2)=graphVector j (fun z => p z.1 z.2) := by
    funext i k
    exact eval_graphPolynomial _ _ _ _
  rw [PolynomialSubspaceCovectorCharts.subspace,hv,graphVector_span]
  exact hp

/-- All ordinary Grassmann charts and all actual image ranks occur in one
shared coefficient/slice open. -/
theorem generic_parameter_inequality
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
      (∃ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,ell ≠ 0 →
        ((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) →
        let d := finrank K (LinearMap.ker (relationMap mu ell))
        let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
        (q*(a-d)+s:ℕ) ≤ (d*(a-d):ℕ)+(T:ℤ)-(e:ℤ)-1 := by
  classical
  let C := Fin (a+1) × Fin (T+1)
  have hc (c : C) :
      ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q s))) K,
        (∃ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0) ∧
        ∀ x : SharedCovectorPolynomial.Input K b T q s,eval (coordinates K _ x) P ≠ 0 →
          ∀ ell : Fin T → K,ell ≠ 0 →
          finrank K (LinearMap.ker (relationMap mu ell))=c.1.val →
          finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))=c.2.val →
          (c.1.val*(a-c.1.val):ℕ)+(T:ℤ)-(c.2.val:ℤ)-1 < (q*(a-c.1.val)+s:ℕ) →
          ¬((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) := by
    by_cases hcount : (c.1.val*(a-c.1.val):ℕ)+(T:ℤ)-(c.2.val:ℤ)-1 < (q*(a-c.1.val)+s:ℕ)
    · obtain ⟨P,hP,hgood⟩ := SlicedCovectorAvoidance.principal_open_excludes_sliced_stratum_of_int_bound
        (d := c.1.val) (e := c.2.val) (q := q) (s := s) mu
        (fun j : Fin c.1.val ↪ Fin a => graphPolynomial j) (c.1.val*(a-c.1.val):ℕ)
        (by intro j; simp only [GraphParameters,Fintype.card_prod,SubspaceCharts.card_outside,
          Fintype.card_fin,Nat.mul_comm]; exact le_rfl) hcount
      exact ⟨P,hP,fun x hx ell hell hd he _ =>
        hgood x hx ell hell hd (graph_covered _ hd) (by omega)⟩
    · refine ⟨1,⟨0,by simp⟩,?_⟩
      intro x hx ell hell hd he hbad
      exact False.elim (hcount hbad)
  choose P hP hgood using hc
  have hne (c : C) : P c ≠ 0 := by
    obtain ⟨x,hx⟩ := hP c
    intro h
    simp [h] at hx
  obtain ⟨z,hz⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ c,P c,⟨(coordinates K _).symm z,?_⟩,?_⟩
  · simpa only [LinearEquiv.apply_symm_apply,map_prod] using
      Finset.prod_ne_zero_iff.mpr (fun c _ => hz c)
  intro x hx ell hell hann
  dsimp only
  by_contra! hbad
  have hd : finrank K (LinearMap.ker (relationMap mu ell)) ≤ a := by
    simpa using (LinearMap.ker (relationMap mu ell)).finrank_le
  have he : finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))) ≤ T := by
    simpa using (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))).finrank_le
  let c : C := (⟨finrank K (LinearMap.ker (relationMap mu ell)),by omega⟩,
    ⟨finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell))),by omega⟩)
  have hxP : eval (coordinates K _ x) (P c) ≠ 0 := by
    rw [map_prod] at hx
    exact Finset.prod_ne_zero_iff.mp hx c (Finset.mem_univ c)
  exact hgood c x hxP ell hell rfl rfl hbad hann

/-- The actual clipped rank budget decreases with the kernel dimension. -/
def sliceCount (k h c J d : ℕ) : ℕ := (k-4*d)+(h-c*d)+(J-(k+h))

theorem sliceCount_antitone (k h c J : ℕ) : Antitone (sliceCount k h c J) := by
  intro u v huv
  unfold sliceCount
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.sub_le_sub_left (by omega) _)
    (Nat.sub_le_sub_left (Nat.mul_le_mul_left c huv) _)) _

/-- Every exact kernel and image rank is included in the closed threshold. -/
theorem principal_open_closed_threshold
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (slices : ℕ → ℕ) (hmono : Antitone slices) (d : ℕ)
    (hcount : ∀ ell : Fin T → K,ell ≠ 0 →
      let u := finrank K (LinearMap.ker (relationMap mu ell))
      let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
      (u*(a-u):ℕ)+(T:ℤ)-(e:ℤ)-1 < (q*(a-u)+slices u:ℕ)) :
    ∃ P : MvPolynomial (Fin (finrank K (SharedCovectorPolynomial.Input K b T q (slices d)))) K,
      (∃ x : SharedCovectorPolynomial.Input K b T q (slices d),eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : SharedCovectorPolynomial.Input K b T q (slices d),eval (coordinates K _ x) P ≠ 0 →
        ∀ ell : Fin T → K,d ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
        ((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 j)=0)) → ell=0 := by
  obtain ⟨P,hP,hgood⟩ := generic_parameter_inequality (q := q) (s := slices d) mu
  refine ⟨P,hP,?_⟩
  intro x hx ell hd hann
  by_contra hell
  have h := hgood x hx ell hell hann
  have hc := hcount ell hell
  have hm := hmono hd
  dsimp only at h hc
  omega

omit [Infinite K] in
/-- The scalar test supplies the strict chart count; the two endpoint
kernels are handled by source generation and the auxiliary-column budget. -/
theorem strict_count_of_scalar
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (k h c : ℕ) (hqa : q*a ≤ T) (hfull : BilinearImage.image mu ⊤=⊤)
    (hscalar : ∀ S : Submodule K (Fin a → K),0 < finrank K S → finrank K S < a →
      UniformScalar.covectorR ((T-q*a:ℕ):ℝ) (finrank K (BilinearImage.image mu S)) q a (finrank K S) < 0 ∨
      UniformScalar.covectorR ((T-q*a:ℕ):ℝ) (finrank K (BilinearImage.image mu S)) q a (finrank K S) -
        UniformScalar.codimensionR k h c (finrank K S) ≤ max (((T-q*a:ℕ):ℝ)-((k+h:ℕ):ℝ)) 0-1)
    (ell : Fin T → K) (hell : ell ≠ 0) :
    let u := finrank K (LinearMap.ker (relationMap mu ell))
    let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
    (u*(a-u):ℕ)+(T:ℤ)-(e:ℤ)-1 < (q*(a-u)+sliceCount k h c (T-q*a) u:ℕ) := by
  let S := LinearMap.ker (relationMap mu ell)
  have he := PolynomialSubspaceCovectorCharts.image_finrank_lt mu S ell hell
    (kernel_image_annihilated mu ell)
  have hdim : finrank K S ≤ a := by simpa using S.finrank_le
  have hlt : finrank K S < a := by
    by_contra! hn
    have htop : S=⊤ := Submodule.eq_top_of_finrank_eq (by simp only [Module.finrank_fin_fun]; omega)
    rw [htop,hfull,finrank_top,Module.finrank_fin_fun] at he
    omega
  dsimp only
  by_cases hz : finrank K S=0
  · have hz' : finrank K (LinearMap.ker (relationMap mu ell))=0 := hz
    rw [hz']
    simp only [Nat.sub_zero,Nat.zero_mul,Nat.cast_zero,zero_add,sliceCount,Nat.mul_zero]
    have htarget : T ≤ q*a+k+h+(T-q*a-(k+h)) := by omega
    omega
  · have hs := ScalarJointCount.strict_joint_budget a T q (finrank K S)
      (finrank K (BilinearImage.image mu S)) k h c hdim he hqa (hscalar S (by omega) hlt)
    have hpos : 1 ≤ finrank K S*(a-finrank K S)+(T-finrank K (BilinearImage.image mu S)) := by omega
    have hc : ((finrank K S*(a-finrank K S)+(T-finrank K (BilinearImage.image mu S))-1:ℕ):ℤ)=
        (finrank K S*(a-finrank K S):ℕ)+(T:ℤ)-(finrank K (BilinearImage.image mu S):ℤ)-1 := by
      rw [Nat.cast_sub hpos,Nat.cast_add,Nat.cast_sub he.le,Nat.cast_one]
      ring
    have hsZ := Int.ofNat_lt.mpr hs
    rw [hc] at hsZ
    simpa only [sliceCount,Nat.add_assoc,S] using hsZ

abbrev Input (K : Type*) [Field K] (a b T q : ℕ) (slices : ℕ → ℕ) :=
  (Fin q → Fin b → K) × ((d : Fin (a+1)) → Fin (slices d.val) → Fin T → K)

def projection (slices : ℕ → ℕ) (d : Fin (a+1)) :
    Input K a b T q slices →ₗ[K] SharedCovectorPolynomial.Input K b T q (slices d.val) where
  toFun x := (x.1,x.2 d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Infinite K] in
theorem projection_surjective (slices : ℕ → ℕ) (d : Fin (a+1)) :
    Function.Surjective (projection (K := K) (b := b) (T := T) (q := q) slices d) := by
  classical
  intro x
  refine ⟨(x.1,Function.update 0 d x.2),?_⟩
  simp only [projection,LinearMap.coe_mk,AddHom.coe_mk,Function.update_self]

/-- One child tuple and all threshold slices are chosen simultaneously. -/
theorem principal_open_all_thresholds
    (mu : (Fin b → K) →ₗ[K] (Fin a → K) →ₗ[K] (Fin T → K))
    (slices : ℕ → ℕ) (hmono : Antitone slices)
    (hcount : ∀ ell : Fin T → K,ell ≠ 0 →
      let u := finrank K (LinearMap.ker (relationMap mu ell))
      let e := finrank K (BilinearImage.image mu (LinearMap.ker (relationMap mu ell)))
      (u*(a-u):ℕ)+(T:ℤ)-(e:ℤ)-1 < (q*(a-u)+slices u:ℕ)) :
    ∃ P : MvPolynomial (Fin (finrank K (Input K a b T q slices))) K,
      (∃ x : Input K a b T q slices,eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : Input K a b T q slices,eval (coordinates K _ x) P ≠ 0 →
        ∀ d : Fin (a+1),∀ ell : Fin T → K,
          d.val ≤ finrank K (LinearMap.ker (relationMap mu ell)) →
          ((∀ i v,covector ell (mu (x.1 i) v)=0) ∧ (∀ j,covector ell (x.2 d j)=0)) → ell=0 := by
  classical
  choose P hP hgood using fun d : Fin (a+1) => principal_open_closed_threshold mu slices hmono d.val hcount
  let pi (d : Fin (a+1)) := (coordinates K _).toLinearMap.comp
    ((projection (K := K) (b := b) (T := T) (q := q) slices d).comp (coordinates K _).symm.toLinearMap)
  let pulled (d : Fin (a+1)) := MiddleCoordinates.substituteLinear (pi d) (P d)
  have hpull (d : Fin (a+1)) : pulled d ≠ 0 := by
    obtain ⟨x,hx⟩ := hP d
    obtain ⟨y,hy⟩ := projection_surjective slices d x
    have hev : eval (coordinates K _ y) (pulled d) ≠ 0 := by
      simpa only [pulled,MiddleCoordinates.eval_substituteLinear,pi,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,hy] using hx
    intro hzero
    exact hev (by rw [hzero,map_zero])
  have hp : (∏ d,pulled d) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun d _ => hpull d)
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero hp
  refine ⟨∏ d,pulled d,⟨(coordinates K _).symm z,by simpa only [LinearEquiv.apply_symm_apply] using hz⟩,?_⟩
  intro x hx d ell hd hann
  have hpd : eval (coordinates K _ x) (pulled d) ≠ 0 := by
    rw [map_prod] at hx
    exact Finset.prod_ne_zero_iff.mp hx d (Finset.mem_univ d)
  apply hgood d (projection slices d x) _ ell hd hann
  simpa only [pulled,MiddleCoordinates.eval_substituteLinear,pi,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hpd

end Quartic.ExpansionClosedSlices
