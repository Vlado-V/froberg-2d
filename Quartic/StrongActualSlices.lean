module

public import Quartic.ActualExpansionSlices
public import Quartic.StrongExpansionOpen
public import Quartic.FixedBlockChildOpen
public import Froberg.FreezeParameters

@[expose] public section

/-! Closed scalar slices with an arbitrary correction-space dimension.
The full convolution surplus permits every nonnegative correction count;
no expected Hilbert function for the child quotient is used. -/
noncomputable section
namespace Quartic.StrongActualSlices
open Module MvPolynomial RowMultiplicationCoordinates HomogeneousCoefficientCoordinates
open UniformEndpoint ProfileCertificate PolynomialBilinearCoordinates
open BilinearCovectorCharts BilinearCoefficientKernel ConvolutionClosedSlices
open ActualExpansionSlices
variable {K : Type*} [Field K]
set_option maxHeartbeats 1500000

def slices (m : ℕ) (upper : Bool) (S : ℕ) : ℕ → ℕ :=
  ExpansionClosedSlices.sliceCount (2*m+2*mixedCount m upper) S
    (mixedCount m upper) (Counts.j m (upperEndpoint m) (mixedCount m upper)).toNat

/-- The scalar implication is independent of the correction count `S`. -/
theorem scalar_bounds_of_uniform_surplus (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (S d E : ℝ) (hdlo : 0<d) (hdhi : d<(totalA m (mixedCount m upper) : ℝ))
    (hE : (UniformScalar.targetCount m (mixedCount m upper) : ℝ) /
      (totalA m (mixedCount m upper) : ℝ)*d +
      (m : ℝ)^2/100*min d ((totalA m (mixedCount m upper) : ℝ)-d) ≤ E) :
    UniformScalar.covectorR (Counts.j m (upperEndpoint m) (mixedCount m upper))
      E (upperEndpoint m) (totalA m (mixedCount m upper)) d < 0 ∨
    UniformScalar.covectorR (Counts.j m (upperEndpoint m) (mixedCount m upper))
      E (upperEndpoint m) (totalA m (mixedCount m upper)) d -
      UniformScalar.codimensionR (2*m+2*mixedCount m upper) S (mixedCount m upper) d ≤
      max ((Counts.j m (upperEndpoint m) (mixedCount m upper) : ℝ)-
        (2*m+2*mixedCount m upper+S)) 0-1 := by
  have hdom := UniformScalar.actual_domination m hm upper
  have hTa : (UniformScalar.targetCount m (mixedCount m upper) : ℝ) /
      (totalA m (mixedCount m upper) : ℝ) =
      (upperEndpoint m : ℝ) + (Counts.j m (upperEndpoint m) (mixedCount m upper) : ℝ) /
        (totalA m (mixedCount m upper) : ℝ) := by
    rw [UniformScalar.target_count_identity m hm upper, add_div,
      mul_div_cancel_right₀ _ (ne_of_gt hdom.1)]
  have hE' : UniformScalar.uniformLower (upperEndpoint m)
      (Counts.j m (upperEndpoint m) (mixedCount m upper))
      (totalA m (mixedCount m upper)) ((m : ℝ)^2/100) d ≤ E := by
    unfold UniformScalar.uniformLower
    simpa only [hTa] using hE
  exact UniformScalar.normal_of_uniform_surplus _ _ _ _ _ _ _ _ _ _
    hdom.1 rfl hdlo hdhi hdom.2.2.2.1 hdom.2.2.2.2.1 hE'

/-- Actual quotient images inherit the normal incidence inequality for every
chosen correction count. -/
theorem actual_scalar_bounds (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (S₀ : ℕ)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : StrongExpansionOpen.Dimensions m upper → ℕ)
    (hE : StrongExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : StrongExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (eV : Source g ≃ₗ[K] (Fin (totalA m (mixedCount m upper)) → K))
    (eW : Target g ≃ₗ[K] (Fin (finrank K (Target g)) → K))
    (S : Submodule K (Fin (totalA m (mixedCount m upper)) → K))
    (hlo : 0 < finrank K S) (hhi : finrank K S < totalA m (mixedCount m upper)) :
    let T := finrank K (Target g)
    let a := totalA m (mixedCount m upper)
    let e := finrank K (BilinearImage.image (actualMu g eV eW) S)
    UniformScalar.covectorR ((T-upperEndpoint m*a:ℕ):ℝ) e (upperEndpoint m) a (finrank K S) < 0 ∨
      UniformScalar.covectorR ((T-upperEndpoint m*a:ℕ):ℝ) e (upperEndpoint m) a (finrank K S) -
        UniformScalar.codimensionR (2*m+2*mixedCount m upper) S₀
          (mixedCount m upper) (finrank K S) ≤
        max (((T-upperEndpoint m*a:ℕ):ℝ)-((2*m+2*mixedCount m upper+S₀:ℕ):ℝ)) 0-1 := by
  let d : StrongExpansionOpen.Dimensions m upper := ⟨finrank K S,by omega⟩
  have hz := hexp 0
  simp only [Fin.val_zero,zero_add] at hz
  have himage : E d ≤ finrank K (BilinearImage.image (actualMu g eV eW) S) := by
    rw [ActualExpansionSlices.actual_image_finrank]
    apply ExpansionCommonOpen.quotient_expansion g hg (E 0) hz (hexp d)
    exact eV.symm.finrank_map_eq S
  have hb := scalar_bounds_of_uniform_surplus m hm upper S₀ (finrank K S)
    (finrank K (BilinearImage.image (actualMu g eV eW) S))
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    ((hE d).2.trans (by exact_mod_cast himage))
  have hsur := (surplus_cast m (by omega) upper g hg (E 0) hz).2
  have hsurR : ((finrank K (Target g)-upperEndpoint m*totalA m (mixedCount m upper):ℕ):ℝ)=
      (Counts.j m (upperEndpoint m) (mixedCount m upper):ℝ) := by exact_mod_cast hsur
  dsimp only
  rw [hsurR]
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hb

/-- On an actual expanded mixed presentation, one genuine principal open
chooses a shared child tuple and all closed-threshold slices. -/
theorem principal_open_actual_slices [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (S : ℕ)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : StrongExpansionOpen.Dimensions m upper → ℕ)
    (hE : StrongExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : StrongExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (eV : Source g ≃ₗ[K] (Fin (totalA m (mixedCount m upper)) → K))
    (eW : Target g ≃ₗ[K] (Fin (finrank K (Target g)) → K)) :
    ∃ P : MvPolynomial (Fin (finrank K (ExpansionClosedSlices.Input K
        (totalA m (mixedCount m upper)) (FormCount m 2) (finrank K (Target g))
        (upperEndpoint m) (slices m upper S)))) K,
      (∃ x : ExpansionClosedSlices.Input K (totalA m (mixedCount m upper)) (FormCount m 2)
        (finrank K (Target g)) (upperEndpoint m) (slices m upper S),eval (coordinates K _ x) P ≠ 0) ∧
      ∀ x : ExpansionClosedSlices.Input K (totalA m (mixedCount m upper)) (FormCount m 2)
          (finrank K (Target g)) (upperEndpoint m) (slices m upper S),eval (coordinates K _ x) P ≠ 0 →
        ∀ d : StrongExpansionOpen.Dimensions m upper,∀ ell : Fin (finrank K (Target g)) → K,
          d.val ≤ finrank K (LinearMap.ker (relationMap (actualMu g eV eW) ell)) →
          ((∀ i v,covector ell (actualMu g eV eW (x.1 i) v)=0) ∧
            (∀ j,covector ell (x.2 d j)=0)) → ell=0 := by
  have hz := hexp 0
  simp only [Fin.val_zero,zero_add] at hz
  have hsur := surplus_cast m (by omega) upper g hg (E 0) hz
  have hsurN : finrank K (Target g)-upperEndpoint m*totalA m (mixedCount m upper)=
      (Counts.j m (upperEndpoint m) (mixedCount m upper)).toNat := by omega
  apply ExpansionClosedSlices.principal_open_all_thresholds (actualMu g eV eW)
    (slices m upper S) (ExpansionClosedSlices.sliceCount_antitone _ _ _ _)
  intro ell hell
  have h := ExpansionClosedSlices.strict_count_of_scalar (actualMu g eV eW)
    (2*m+2*mixedCount m upper) S (mixedCount m upper) hsur.1
    (actual_image_top g eV eW) (by
      intro W hlo hhi
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
        actual_scalar_bounds m hm upper S g hg E hE hexp eV eW W hlo hhi) ell hell
  simpa only [hsurN,slices] using h

/-- An arbitrary additional child-coefficient principal open can be
intersected without changing the fixed mixed presentation or any threshold. -/
theorem exists_ambient_slices_in_open [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (S : ℕ)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : StrongExpansionOpen.Dimensions m upper → ℕ)
    (hE : StrongExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : StrongExpansionOpen.Dimensions m upper,RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (D : MvPolynomial (Fin (upperEndpoint m) × Fin (FormCount m 2)) K)
    (hD : ∃ Q,eval Q D ≠ 0) :
    ∃ Q : Fin (upperEndpoint m) → Forms K m 2,
      eval (fun i => finiteEquiv (Q i.1) i.2) D ≠ 0 ∧
      ∃ Z : (d : StrongExpansionOpen.Dimensions m upper) → Fin (slices m upper S d.val) → Rows K m 3,
        ∀ d : StrongExpansionOpen.Dimensions m upper,∀ lam : Fin (RowCount m 3) → K,
          d.val+mixedCount m upper ≤ finrank K (LinearMap.ker
            (relationMap RowMultiplicationCoordinates.coordinate lam)) →
          (∀ j f,covector lam (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
          (∀ i v,covector lam (RowMultiplicationCoordinates.coordinate (finiteEquiv (Q i)) v)=0) →
          (∀ j,covector lam (rowFiniteEquiv (Z d j))=0) → lam=0 := by
  classical
  let a := totalA m (mixedCount m upper)
  have ha : finrank K (Source g)=a := by
    rw [ExpansionCommonOpen.linear_quotient_dimension g hg]
    have hc := ConvolutionAllRange.endpoint_columns_range m (by omega) upper
    exact (totalA_eq m _ hc.1 hc.2).symm
  let eV : Source g ≃ₗ[K] (Fin a → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using ha)
  let eW := coordinates K (Target g)
  let V := ExpansionClosedSlices.Input K a (FormCount m 2) (finrank K (Target g)) (upperEndpoint m) (slices m upper S)
  obtain ⟨P,hP,hgood⟩ := principal_open_actual_slices m hm upper S g hg E hE hexp eV eW
  let childProjection : V →ₗ[K] (Fin (upperEndpoint m) × Fin (FormCount m 2) → K) :=
    { toFun := fun x i => x.1 i.1 i.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f := childProjection.comp (coordinates K V).symm.toLinearMap
  let D' := MiddleCoordinates.substituteLinear f D
  have hDn : D' ≠ 0 := by
    obtain ⟨Q,hQ⟩ := hD
    let x : V := (fun i j => Q (i,j),0)
    have hx : eval (coordinates K V x) D' ≠ 0 := by
      simpa only [D',MiddleCoordinates.eval_substituteLinear,f,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,childProjection,LinearMap.coe_mk,
        AddHom.coe_mk,x] using hQ
    intro hz
    exact hx (by rw [hz,map_zero])
  have hPn : P ≠ 0 := by
    obtain ⟨x,hx⟩ := hP
    intro hz
    exact hx (by rw [hz,map_zero])
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero (mul_ne_zero hPn hDn)
  rw [map_mul,mul_ne_zero_iff] at hz
  let x : V := (coordinates K V).symm z
  have hx : eval (coordinates K V x) P ≠ 0 := by simpa only [x,LinearEquiv.apply_symm_apply] using hz.1
  obtain ⟨Z,hZ⟩ := lift_closed_slices_coordinates g hg eV eW (slices m upper S) x (hgood x hx)
  refine ⟨fun i => finiteEquiv.symm (x.1 i),?_,Z,?_⟩
  · have hh : eval (childProjection x) D ≠ 0 := by
      simpa only [D',MiddleCoordinates.eval_substituteLinear,f,LinearMap.comp_apply,LinearEquiv.coe_coe,x] using hz.2
    simpa only [LinearEquiv.apply_symm_apply,childProjection,LinearMap.coe_mk,AddHom.coe_mk] using hh
  · simpa only [LinearEquiv.apply_symm_apply] using hZ


/-- Literal ambient closed slices for the fixed mixed and child families. -/
def HasAmbientSlices {m : ℕ} {upper : Bool}
    (g : Fin (mixedCount m upper) → Rows K m 1) (S : ℕ)
    (Q : Fin (upperEndpoint m) → Forms K m 2) : Prop :=
  ∃ Z : (d : StrongExpansionOpen.Dimensions m upper) →
      Fin (slices m upper S d.val) → Rows K m 3,
    ∀ d : StrongExpansionOpen.Dimensions m upper, ∀ lam : Fin (RowCount m 3) → K,
      d.val+mixedCount m upper ≤ finrank K (LinearMap.ker
        (relationMap RowMultiplicationCoordinates.coordinate lam)) →
      (∀ j f, covector lam (RowMultiplicationCoordinates.coordinate f (rowFiniteEquiv (g j)))=0) →
      (∀ i v, covector lam (RowMultiplicationCoordinates.coordinate (finiteEquiv (Q i)) v)=0) →
      (∀ j, covector lam (rowFiniteEquiv (Z d j))=0) → lam=0

/-- Freezing one successful set of cuts gives a genuine nonempty open in the
child coefficients alone. This permits later intersection across correction
counts and with any independently prescribed child open. -/
theorem child_slices_open [Infinite K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (S : ℕ)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : StrongExpansionOpen.Dimensions m upper → ℕ)
    (hE : StrongExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : StrongExpansionOpen.Dimensions m upper, RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2)) :
    ∃ D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        HasAmbientSlices g S (FixedBlockChildOpen.decode a) := by
  classical
  let a := totalA m (mixedCount m upper)
  have ha : finrank K (Source g)=a := by
    rw [ExpansionCommonOpen.linear_quotient_dimension g hg]
    have hc := ConvolutionAllRange.endpoint_columns_range m (by omega) upper
    exact (totalA_eq m _ hc.1 hc.2).symm
  let eV : Source g ≃ₗ[K] (Fin a → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using ha)
  let eW := coordinates K (Target g)
  let U := Fin (upperEndpoint m) → Fin (FormCount m 2) → K
  let V := (d : Fin (a+1)) → Fin (slices m upper S d.val) → Fin (finrank K (Target g)) → K
  obtain ⟨P,hP,hgood⟩ := principal_open_actual_slices m hm upper S g hg E hE hexp eV eW
  obtain ⟨cuts,B,⟨u,hu⟩,hB⟩ := Froberg.principal_open_freeze_right
    (U := U) (V := V) P hP _ hgood
  let curry : (FixedBlockChildOpen.ChildIndex m (upperEndpoint m) → K) →ₗ[K] U :=
    { toFun := fun z i j => z (i,j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let F := (coordinates K U).toLinearMap.comp curry
  let D := MiddleCoordinates.substituteLinear F B
  have heval (z : FixedBlockChildOpen.ChildIndex m (upperEndpoint m) → K) :
      eval z D=eval (coordinates K U (curry z)) B := by
    simp only [D,MiddleCoordinates.eval_substituteLinear,F,LinearMap.comp_apply,LinearEquiv.coe_coe]
  refine ⟨D,⟨fun i => u i.1 i.2,?_⟩,?_⟩
  · rw [heval]
    exact hu
  · intro z hz
    rw [heval] at hz
    have hx := hB (curry z) hz
    obtain ⟨Z,hZ⟩ := lift_closed_slices_coordinates g hg eV eW (slices m upper S)
      (curry z,cuts) hx
    refine ⟨Z,?_⟩
    intro d lam hd hmixed hchild hcuts
    apply hZ d lam hd hmixed _ hcuts
    intro i v
    have hdecode : finiteEquiv ((FixedBlockChildOpen.decode z) i)=curry z i := by
      exact finiteEquiv.apply_symm_apply _
    simpa only [hdecode] using hchild i v

/-- One child tuple works for every member of any finite family of correction
counts and lies in the prescribed nonempty child-coordinate open. -/
theorem exists_all_corrections_in_open [Infinite K]
    {I : Type*} [Fintype I] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (correction : I → ℕ)
    (g : Fin (mixedCount m upper) → Rows K m 1) (hg : LinearIndependent K g)
    (E : StrongExpansionOpen.Dimensions m upper → ℕ)
    (hE : StrongExpansionOpen.Thresholds m upper E)
    (hexp : ∀ d : StrongExpansionOpen.Dimensions m upper, RowExpansionOpen.Expands g
      (d.val+mixedCount m upper) (E d+mixedCount m upper*(m+1).choose 2))
    (D : MvPolynomial (FixedBlockChildOpen.ChildIndex m (upperEndpoint m)) K)
    (hD : ∃ z, eval z D ≠ 0) :
    ∃ Q : Fin (upperEndpoint m) → Forms K m 2,
      eval (FixedBlockChildOpen.encodeChild Q) D ≠ 0 ∧
      ∀ i, HasAmbientSlices g (correction i) Q := by
  classical
  choose P hP hgood using fun i => child_slices_open m hm upper (correction i) g hg E hE hexp
  have hnz (i : I) : P i ≠ 0 := by
    obtain ⟨z,hz⟩ := hP i
    intro h; exact hz (by rw [h,map_zero])
  have hDn : D ≠ 0 := by
    obtain ⟨z,hz⟩ := hD
    intro h; exact hz (by rw [h,map_zero])
  obtain ⟨z,hz⟩ := PolynomialImageAvoidance.exists_eval_ne_zero
    (mul_ne_zero hDn (Finset.prod_ne_zero_iff.mpr (fun i _ => hnz i)))
  change eval z (D * ∏ i, P i) ≠ 0 at hz
  rw [map_mul,mul_ne_zero_iff] at hz
  refine ⟨FixedBlockChildOpen.decode z,?_,?_⟩
  · simpa only [FixedBlockChildOpen.encode_decode] using hz.1
  · intro i
    apply hgood i z
    exact Finset.prod_ne_zero_iff.mp (by simpa only [map_prod] using hz.2)
      i (Finset.mem_univ i)

/-- Correction dimension for an actual marked subspace of dimension `w`. -/
def markedCorrectionCount (m : ℕ) (upper : Bool) (w : ℕ) : ℕ :=
  (Counts.H m (upperEndpoint m) (mixedCount m upper)).toNat+3+w

theorem markedCorrectionCount_cast (m : ℕ) (hm : 320 ≤ m) (upper : Bool) (w : ℕ) :
    (markedCorrectionCount m upper w : ℤ)=
      Counts.H m (upperEndpoint m) (mixedCount m upper)+3+w := by
  have hH := (UniformScalar.structural_dimension_signs m hm upper).2.1
  simp only [markedCorrectionCount,Nat.cast_add,Nat.cast_ofNat,Int.toNat_of_nonneg hH]

/-- The literal motion budget, without replacing the marked dimension by an
expected Hilbert function. -/
theorem slices_eq (m : ℕ) (upper : Bool) (S d : ℕ) :
    slices m upper S d = (2*m+2*mixedCount m upper-4*d)+
      (S-mixedCount m upper*d)+
      (Counts.j m (upperEndpoint m) (mixedCount m upper)-
        ((2*m+2*mixedCount m upper:ℕ):ℤ)-S).toNat := by
  unfold slices ExpansionClosedSlices.sliceCount
  congr 1
  omega

end Quartic.StrongActualSlices
