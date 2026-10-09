module

public import Quartic.SubspaceCharts
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic

@[expose] public section

/-!
# Explicit two-block charts for subspaces

The two initial pieces of a subspace of V × W are its intersection with V
and its projection to W. In fixed coordinate charts on these pieces, the
remaining extension is represented by a matrix from the selected W
coordinates to the unselected V coordinates.
-/

noncomputable section
namespace Quartic.BlockSubspaceCharts
open Module SubspaceCharts

section Abstract
variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The first initial piece, identified with a subspace of the first block. -/
def lower (S : Submodule K (V × W)) : Submodule K V :=
  S.comap (LinearMap.inl K V W)

/-- The second initial piece is the projection to the second block. -/
def upper (S : Submodule K (V × W)) : Submodule K W :=
  S.map (LinearMap.snd K V W)

@[simp] theorem mem_lower (S : Submodule K (V × W)) (x : V) :
    x ∈ lower S ↔ (x, 0) ∈ S := Iff.rfl

@[simp] theorem mem_upper (S : Submodule K (V × W)) (y : W) :
    y ∈ upper S ↔ ∃ x : V, (x, y) ∈ S := by
  constructor
  · rintro ⟨⟨x, y'⟩, h, he⟩
    change y' = y at he
    subst y'
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨(x,y),h,rfl⟩

/-- Projection onto the actual second initial piece. -/
def upperProjection (S : Submodule K (V × W)) : S →ₗ[K] upper S :=
  ((LinearMap.snd K V W).comp S.subtype).codRestrict (upper S)
    (fun x => ⟨x.val,x.property,rfl⟩)

theorem upperProjection_surjective (S : Submodule K (V × W)) :
    Function.Surjective (upperProjection S) := by
  rintro ⟨y,hy⟩
  obtain ⟨x,hx⟩ := (mem_upper S y).mp hy
  exact ⟨⟨(x,y),hx⟩,rfl⟩

/-- Every subspace has an actual linear lift of its second initial piece. -/
theorem exists_extension (S : Submodule K (V × W)) :
    ∃ f : upper S →ₗ[K] V, ∀ y : upper S, (f y,y.val) ∈ S := by
  obtain ⟨g,hg⟩ := (upperProjection S).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (upperProjection_surjective S))
  refine ⟨(LinearMap.fst K V W).comp (S.subtype.comp g),fun y => ?_⟩
  have he : (g y).val.2 = y.val := congrArg Subtype.val (LinearMap.congr_fun hg y)
  change ((g y).val.1,y.val) ∈ S
  rw [← he]
  exact (g y).property

/-- Subtracting a chosen lift leaves precisely the first initial piece. -/
theorem mem_iff_extension (S : Submodule K (V × W))
    (f : upper S →ₗ[K] V) (hf : ∀ y : upper S, (f y,y.val) ∈ S)
    (x : V) (y : upper S) : (x,y.val) ∈ S ↔ x-f y ∈ lower S := by
  constructor
  · intro h
    have hs := S.sub_mem h (hf y)
    simpa only [Prod.mk_sub_mk, sub_self, mem_lower] using hs
  · intro h
    have hs := S.add_mem ((mem_lower S _).mp h) (hf y)
    simpa only [Prod.mk_add_mk, sub_add_cancel, zero_add] using hs

/-- In quotient language the extension is an actual graph over the second piece. -/
theorem mem_iff_quotient_extension (S : Submodule K (V × W))
    (f : upper S →ₗ[K] V) (hf : ∀ y : upper S, (f y,y.val) ∈ S)
    (x : V) (y : upper S) :
    (x,y.val) ∈ S ↔ (lower S).mkQ x=(lower S).mkQ (f y) := by
  rw [mem_iff_extension S f hf x y,← Submodule.Quotient.mk_eq_zero]
  change (lower S).mkQ (x-f y)=0 ↔ _
  rw [map_sub,sub_eq_zero]

/-- The quotient-valued extension is independent of the chosen linear lift. -/
theorem quotient_extension_unique (S : Submodule K (V × W))
    (f g : upper S →ₗ[K] V)
    (hf : ∀ y : upper S, (f y,y.val) ∈ S)
    (hg : ∀ y : upper S, (g y,y.val) ∈ S) :
    (lower S).mkQ.comp f=(lower S).mkQ.comp g := by
  apply LinearMap.ext
  intro y
  exact (mem_iff_quotient_extension S g hg (f y) y).mp (hf y)

/-- The first block agrees with projecting the subspace restricted to the first prefix. -/
theorem lower_eq_first_prefix (S : Submodule K (V × W)) :
    lower S=(S ⊓ LinearMap.ker (LinearMap.snd K V W)).map (LinearMap.fst K V W) := by
  ext x
  constructor
  · intro hx
    exact ⟨(x,0),⟨hx,rfl⟩,rfl⟩
  · rintro ⟨⟨x',y⟩,⟨hS,hy⟩,hx⟩
    change y=0 at hy
    change x'=x at hx
    subst y
    subst x'
    exact hS

/-- At the second prefix all source vectors are allowed, so the piece is the projection. -/
theorem upper_eq_second_prefix (S : Submodule K (V × W)) :
    upper S=(S ⊓ ⊤).map (LinearMap.snd K V W) := by simp [upper]

end Abstract

variable {K : Type*} [Field K] {v w r s : ℕ}

/-- Scalar coefficients of the extension between two fixed block charts. -/
abbrev Extension (K : Type*) (j : Fin r ↪ Fin v) (s : ℕ) := Outside j → Fin s → K

/-- All parameters of a fixed two-block chart. -/
abbrev Parameters (K : Type*) [Field K] (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) :=
  SubspaceCharts.Parameters K j × SubspaceCharts.Parameters K k × Extension K j s

/-- The actual extension matrix as a linear map. -/
def extensionMap {j : Fin r ↪ Fin v} (C : Extension K j s) :
    (Fin s → K) →ₗ[K] (Outside j → K) :=
  LinearMap.pi fun i => ∑ l, C i l • LinearMap.proj l

@[simp] theorem extensionMap_apply {j : Fin r ↪ Fin v} (C : Extension K j s)
    (y : Fin s → K) (i : Outside j) : extensionMap C y i = ∑ l,C i l*y l := by
  simp [extensionMap]

/-- The graph equations in the first block, modulo its initial subspace. -/
def residual (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j) :
    (Fin v → K) →ₗ[K] (Outside j → K) :=
  outsideProjection j-(parameterMap A).comp (selectedProjection j)

@[simp] theorem residual_apply (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j)
    (x : Fin v → K) (i : Outside j) :
    residual j A x i = x i.val-∑ l,A i l*x (j l) := by
  simp [residual, outsideProjection, selectedProjection]

theorem ker_residual (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j) :
    LinearMap.ker (residual j A) = chartSubspace j A := rfl

/-- A two-block chart is specified by graph equations with polynomial coefficients. -/
def chart (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) (p : Parameters K j k) :
    Submodule K ((Fin v → K) × (Fin w → K)) :=
  (chartSubspace k p.2.1).comap (LinearMap.snd K _ _) ⊓
    LinearMap.ker ((residual j p.1).comp (LinearMap.fst K _ _) -
      (extensionMap p.2.2).comp ((selectedProjection k).comp (LinearMap.snd K _ _)))

@[simp] theorem mem_chart (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) (x : Fin v → K) (y : Fin w → K) :
    (x,y) ∈ chart j k p ↔ y ∈ chartSubspace k p.2.1 ∧
      residual j p.1 x = extensionMap p.2.2 (selectedProjection k y) := by
  change (y ∈ chartSubspace k p.2.1 ∧
    residual j p.1 x-extensionMap p.2.2 (selectedProjection k y)=0) ↔ _
  rw [sub_eq_zero]

/-- Fill only the coordinates outside the first chart's selector. -/
def outsideLift (j : Fin r ↪ Fin v) : (Outside j → K) →ₗ[K] (Fin v → K) := by
  classical
  exact LinearMap.pi fun i => if h:i ∈ Set.range j then 0 else LinearMap.proj ⟨i,h⟩

@[simp] theorem outsideLift_selected (j : Fin r ↪ Fin v) (z : Outside j → K) (i : Fin r) :
    outsideLift j z (j i)=0 := by
  classical
  simp only [outsideLift, LinearMap.pi_apply, dite_eq_left (show j i ∈ Set.range j from ⟨i,rfl⟩),
    LinearMap.zero_apply]

@[simp] theorem outsideLift_outside (j : Fin r ↪ Fin v) (z : Outside j → K) (i : Outside j) :
    outsideLift j z i.val=z i := by
  classical
  simp only [outsideLift, LinearMap.pi_apply, dite_eq_right i.property, LinearMap.proj_apply]

@[simp] theorem selected_chartLift (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j)
    (x : Fin r → K) : selectedProjection j (chartLift j A x)=x := by
  ext i
  exact chartLift_selected j A x i

@[simp] theorem selected_outsideLift (j : Fin r ↪ Fin v) (z : Outside j → K) :
    selectedProjection j (outsideLift j z)=0 := by
  ext i
  exact outsideLift_selected j z i

@[simp] theorem residual_chartLift (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j)
    (x : Fin r → K) : residual j A (chartLift j A x)=0 :=
  chartLift_mem j A x

@[simp] theorem residual_outsideLift (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j)
    (z : Outside j → K) : residual j A (outsideLift j z)=z := by
  ext i
  simp [residual_apply]

/-- The selected component and graph residual reconstruct every first-block vector. -/
theorem decomposition (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j)
    (x : Fin v → K) :
    chartLift j A (selectedProjection j x)+outsideLift j (residual j A x)=x := by
  classical
  ext i
  by_cases hi:i ∈ Set.range j
  · obtain ⟨l,rfl⟩ := hi
    simp only [Pi.add_apply, chartLift_selected, outsideLift_selected, add_zero]
    rfl
  · change chartLift j A (selectedProjection j x) (⟨i,hi⟩ : Outside j).val+
      outsideLift j (residual j A x) (⟨i,hi⟩ : Outside j).val=x i
    rw [chartLift_outside, outsideLift_outside, parameterMap_apply, residual_apply]
    change (∑ l,A ⟨i,hi⟩ l*x (j l))+(x i-∑ l,A ⟨i,hi⟩ l*x (j l))=x i
    abel

theorem chartLift_selected_of_mem (j : Fin r ↪ Fin v) (A : SubspaceCharts.Parameters K j)
    {x : Fin v → K} (hx : x ∈ chartSubspace j A) :
    chartLift j A (selectedProjection j x)=x := by
  have hr : residual j A x=0 := hx
  simpa only [hr,map_zero,add_zero] using decomposition j A x

/-- The polynomial basis map of the two-block chart. -/
def lift (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) (p : Parameters K j k) :
    ((Fin r → K) × (Fin s → K)) →ₗ[K] ((Fin v → K) × (Fin w → K)) :=
  ((chartLift j p.1).coprod ((outsideLift j).comp (extensionMap p.2.2))).prod
    ((chartLift k p.2.1).comp (LinearMap.snd K _ _))

@[simp] theorem lift_apply (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) (x : Fin r → K) (y : Fin s → K) :
    lift j k p (x,y)=
      (chartLift j p.1 x+outsideLift j (extensionMap p.2.2 y),chartLift k p.2.1 y) := rfl

theorem lift_mem (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) (z : (Fin r → K) × (Fin s → K)) :
    lift j k p z ∈ chart j k p := by
  rcases z with ⟨x,y⟩
  rw [lift_apply,mem_chart]
  exact ⟨chartLift_mem _ _ _,by simp⟩

theorem lift_injective (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) : Function.Injective (lift j k p) := by
  rintro ⟨x,y⟩ ⟨x',y'⟩ h
  have hx := congrArg (fun z => selectedProjection j z.1) h
  have hy := congrArg (fun z => selectedProjection k z.2) h
  simp only [lift_apply, map_add, selected_chartLift, selected_outsideLift, add_zero] at hx hy
  exact Prod.ext hx hy

/-- All vectors in the graph equations have the displayed polynomial basis expansion. -/
theorem range_lift (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) : LinearMap.range (lift j k p)=chart j k p := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    exact lift_mem j k p z
  · rintro ⟨x,y⟩ h
    obtain ⟨hy,hx⟩ := (mem_chart j k p x y).mp h
    refine ⟨(selectedProjection j x,selectedProjection k y),?_⟩
    rw [lift_apply,chartLift_selected_of_mem k p.2.1 hy,← hx,decomposition]

theorem chart_finrank (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) : finrank K (chart j k p)=r+s := by
  rw [← range_lift,LinearMap.finrank_range_of_inj (lift_injective j k p)]
  simp

theorem lower_chart (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) : lower (chart j k p)=chartSubspace j p.1 := by
  ext x
  rw [mem_lower,mem_chart]
  simp only [Submodule.zero_mem,map_zero,true_and]
  rfl

theorem upper_chart (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (p : Parameters K j k) : upper (chart j k p)=chartSubspace k p.2.1 := by
  ext y
  rw [mem_upper]
  constructor
  · rintro ⟨x,h⟩
    exact ((mem_chart j k p x y).mp h).1
  · intro hy
    refine ⟨outsideLift j (extensionMap p.2.2 (selectedProjection k y)),?_⟩
    rw [mem_chart]
    exact ⟨hy,residual_outsideLift _ _ _⟩

/-- Every linear extension has exactly the displayed coefficient matrix. -/
theorem extensionMap_of_linear {j : Fin r ↪ Fin v}
    (T : (Fin s → K) →ₗ[K] (Outside j → K)) :
    extensionMap (fun i l => T (Pi.single l 1) i)=T := by
  classical
  apply LinearMap.ext
  intro y
  funext i
  have h := congrArg (fun z => T z i) ((Pi.basisFun K (Fin s)).sum_equivFun y)
  simpa [extensionMap_apply, map_sum, map_smul, Pi.basisFun_apply,
    Pi.basisFun_equivFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- Once charts on the two initial pieces are fixed, only the extension matrix remains. -/
theorem exists_extension_coefficients
    (S : Submodule K ((Fin v → K) × (Fin w → K)))
    (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (A : SubspaceCharts.Parameters K j) (B : SubspaceCharts.Parameters K k)
    (hA : chartSubspace j A=lower S) (hB : chartSubspace k B=upper S) :
    ∃ C : Extension K j s, chart j k (A,B,C)=S := by
  obtain ⟨f,hf⟩ := exists_extension S
  let e : upper S ≃ₗ[K] (Fin s → K) := (LinearEquiv.ofEq _ _ hB.symm).trans (chartEquiv k B)
  have he (y : upper S) : e y=selectedProjection k y.val := rfl
  let T : (Fin s → K) →ₗ[K] (Outside j → K) :=
    (residual j A).comp (f.comp e.symm.toLinearMap)
  let C : Extension K j s := fun i l => T (Pi.single l 1) i
  have hC : extensionMap C=T := extensionMap_of_linear T
  refine ⟨C,?_⟩
  ext ⟨x,y⟩
  rw [mem_chart]
  constructor
  · rintro ⟨hy,hxy⟩
    have hyS : y ∈ upper S := hB ▸ hy
    let y' : upper S := ⟨y,hyS⟩
    have hres : residual j A x=residual j A (f y') := by
      rw [hC,← he y'] at hxy
      simpa only [T,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hxy
    apply (mem_iff_extension S f hf x y').mpr
    rw [← hA]
    change residual j A (x-f y')=0
    rw [map_sub,hres,sub_self]
  · intro hxy
    have hyS : y ∈ upper S := (mem_upper S y).mpr ⟨x,hxy⟩
    let y' : upper S := ⟨y,hyS⟩
    refine ⟨hB.symm ▸ hyS,?_⟩
    have hl := (mem_iff_extension S f hf x y').mp hxy
    rw [← hA] at hl
    change residual j A (x-f y')=0 at hl
    rw [map_sub,sub_eq_zero] at hl
    rw [hC,← he y']
    simpa only [T,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hl

/-- Every subspace with the prescribed two initial dimensions has one of these charts. -/
theorem exists_chart (S : Submodule K ((Fin v → K) × (Fin w → K)))
    (hr : finrank K (lower S)=r) (hs : finrank K (upper S)=s) :
    ∃ j : Fin r ↪ Fin v, ∃ k : Fin s ↪ Fin w,
      ∃ p : Parameters K j k, chart j k p=S := by
  obtain ⟨j,A,hA⟩ := SubspaceCharts.exists_chart (lower S) hr
  obtain ⟨k,B,hB⟩ := SubspaceCharts.exists_chart (upper S) hs
  obtain ⟨C,hC⟩ := exists_extension_coefficients S j k A B hA hB
  exact ⟨j,k,(A,B,C),hC⟩

/-- Exact dimension accounting for the two initial pieces. -/
theorem lower_add_upper_finrank (S : Submodule K ((Fin v → K) × (Fin w → K))) :
    finrank K (lower S)+finrank K (upper S)=finrank K S := by
  obtain ⟨j,k,p,hp⟩ := exists_chart S rfl rfl
  have h := chart_finrank j k p
  rw [hp] at h
  exact h.symm

/-- The extension contributes s(v-r) freely chosen scalar coefficients. -/
theorem extension_finrank (j : Fin r ↪ Fin v) :
    finrank K (Extension K j s)=s*(v-r) := by
  classical
  simp only [Extension, Module.finrank_pi_fintype, finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [card_outside,mul_comm]

/-- The full two-block chart has precisely the required number of scalar parameters. -/
theorem parameters_finrank (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) :
    finrank K (Parameters K j k)=r*(v-r)+s*(w-s)+s*(v-r) := by
  change finrank K (SubspaceCharts.Parameters K j × SubspaceCharts.Parameters K k × Extension K j s)=_
  rw [Module.finrank_prod,Module.finrank_prod,
    SubspaceCharts.parameters_finrank,SubspaceCharts.parameters_finrank,extension_finrank]
  omega

/-- A finite set of scalar positions for the three coefficient arrays. -/
abbrev ParameterIndex (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) :=
  (Outside j × Fin r) ⊕ ((Outside k × Fin s) ⊕ (Outside j × Fin s))

theorem parameter_count (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) :
    Fintype.card (ParameterIndex j k)=r*(v-r)+s*(w-s)+s*(v-r) := by
  classical
  simp only [ParameterIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,card_outside]
  ring

/-- The three arrays are precisely an affine coordinate space of the stated size. -/
def decode (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w) :
    (ParameterIndex j k → K) ≃ₗ[K] Parameters K j k where
  toFun z := (fun i l => z (.inl (i,l)),
    fun i l => z (.inr (.inl (i,l))),fun i l => z (.inr (.inr (i,l))))
  invFun p := Sum.elim (fun a => p.1 a.1 a.2)
    (Sum.elim (fun a => p.2.1 a.1 a.2) (fun a => p.2.2 a.1 a.2))
  left_inv z := by funext i; rcases i with i | (i | i) <;> rfl
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every ambient coordinate of a chart basis combination is a literal polynomial
in the chart parameters. The source coordinates are arbitrary fixed scalars. -/
def liftPolynomial (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (x : Fin r → K) (y : Fin s → K) :
    (Fin v ⊕ Fin w) → MvPolynomial (ParameterIndex j k) K := by
  classical
  exact Sum.elim
    (fun i => if h:i ∈ Set.range j then MvPolynomial.C (x (Classical.choose h)) else
      (∑ l,MvPolynomial.X (.inl (⟨i,h⟩,l))*MvPolynomial.C (x l))+
      ∑ l,MvPolynomial.X (.inr (.inr (⟨i,h⟩,l)))*MvPolynomial.C (y l))
    (fun i => if h:i ∈ Set.range k then MvPolynomial.C (y (Classical.choose h)) else
      ∑ l,MvPolynomial.X (.inr (.inl (⟨i,h⟩,l)))*MvPolynomial.C (y l))

/-- Evaluation recovers the actual first block of the chart lift. -/
theorem eval_liftPolynomial_left (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (z : ParameterIndex j k → K) (x : Fin r → K) (y : Fin s → K) (i : Fin v) :
    MvPolynomial.eval z (liftPolynomial j k x y (.inl i))=
      (lift j k (decode j k z) (x,y)).1 i := by
  classical
  by_cases hi:i ∈ Set.range j
  · obtain ⟨l,rfl⟩ := hi
    have h : j l ∈ Set.range j := ⟨l,rfl⟩
    have he : Classical.choose h=l := j.injective (Classical.choose_spec h)
    simp only [liftPolynomial,Sum.elim_inl,dite_eq_left h,MvPolynomial.eval_C,
      he,lift_apply,Pi.add_apply,chartLift_selected,outsideLift_selected,add_zero]
  · change MvPolynomial.eval z (liftPolynomial j k x y (.inl i))=
      chartLift j (decode j k z).1 x (⟨i,hi⟩ : Outside j).val+
      outsideLift j (extensionMap (decode j k z).2.2 y) (⟨i,hi⟩ : Outside j).val
    rw [chartLift_outside,outsideLift_outside,parameterMap_apply,extensionMap_apply]
    simp only [liftPolynomial,Sum.elim_inl,dite_eq_right hi,map_add,map_sum,map_mul,
      MvPolynomial.eval_X,MvPolynomial.eval_C]
    rfl

/-- Evaluation recovers the actual second block of the chart lift. -/
theorem eval_liftPolynomial_right (j : Fin r ↪ Fin v) (k : Fin s ↪ Fin w)
    (z : ParameterIndex j k → K) (x : Fin r → K) (y : Fin s → K) (i : Fin w) :
    MvPolynomial.eval z (liftPolynomial j k x y (.inr i))=
      (lift j k (decode j k z) (x,y)).2 i := by
  classical
  by_cases hi:i ∈ Set.range k
  · obtain ⟨l,rfl⟩ := hi
    have h : k l ∈ Set.range k := ⟨l,rfl⟩
    have he : Classical.choose h=l := k.injective (Classical.choose_spec h)
    simp only [liftPolynomial,Sum.elim_inr,dite_eq_left h,MvPolynomial.eval_C,
      he,lift_apply,chartLift_selected]
  · change MvPolynomial.eval z (liftPolynomial j k x y (.inr i))=
      chartLift k (decode j k z).2.1 y (⟨i,hi⟩ : Outside k).val
    rw [chartLift_outside,parameterMap_apply]
    simp only [liftPolynomial,Sum.elim_inr,dite_eq_right hi,map_sum,map_mul,
      MvPolynomial.eval_X,MvPolynomial.eval_C]
    rfl

end Quartic.BlockSubspaceCharts
