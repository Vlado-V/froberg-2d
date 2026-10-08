import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Data.Fintype.Card

/-!
# Finite coordinate charts for vector subspaces

Every finite-dimensional subspace of a coordinate space projects isomorphically
onto some set of actual ambient coordinates. On that chart, its remaining
coordinates are linear forms in the selected coordinates. The parameter count
is proved as a vector-space dimension; no geometric dimension statement is
asserted.
-/

noncomputable section
namespace Quartic.SubspaceCharts
open Module
variable {K : Type*} [Field K] {n r : ℕ}

/-- Restriction of an actual ambient coordinate to the subspace. -/
def coordinate (S : Submodule K (Fin n → K)) (i : Fin n) : Dual K S :=
  (LinearMap.proj i).comp S.subtype

@[simp] theorem coordinate_apply (S : Submodule K (Fin n → K)) (i : Fin n) (x : S) :
    coordinate S i x = x.val i := rfl

/-- Restricted ambient coordinates span the whole dual of the subspace. -/
theorem coordinate_span (S : Submodule K (Fin n → K)) :
    Submodule.span K (Set.range (coordinate S)) = ⊤ := by
  let b := (Pi.basisFun K (Fin n)).dualBasis
  have hb := congrArg (Submodule.map S.subtype.dualMap) b.span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearMap.range_eq_top.mpr (LinearMap.dualMap_surjective_of_injective S.injective_subtype)] at hb
  have heq : S.subtype.dualMap ∘ b = coordinate S := by
    funext i
    apply LinearMap.ext
    intro x
    simp [b, coordinate]
  rw [heq] at hb
  exact hb

/-- Some actual ambient coordinates give a complete linear coordinate system on the subspace. -/
theorem exists_coordinate_equiv (S : Submodule K (Fin n → K)) :
    ∃ j : Fin (finrank K S) ↪ Fin n,
      ∃ e : S ≃ₗ[K] (Fin (finrank K S) → K), ∀ x i, e x i = x.val (j i) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (coordinate S)
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Basis κ K (Dual K S) := Basis.mk hli (by rw [hspan, coordinate_span])
  have hcard : Fintype.card κ = finrank K S :=
    (finrank_eq_card_basis b).symm.trans (Subspace.dual_finrank_eq)
  let reindex := Fintype.equivFinOfCardEq hcard
  let b' : Basis (Fin (finrank K S)) K (Dual K S) := b.reindex reindex
  let e : S ≃ₗ[K] (Fin (finrank K S) → K) :=
    (Module.evalEquiv K S).trans b'.dualBasis.equivFun
  refine ⟨⟨fun i => a (reindex.symm i), ha.comp reindex.symm.injective⟩, e, ?_⟩
  intro x i
  simp [e, Basis.dualBasis_equivFun, b', b, coordinate]

/-- Version with a specified dimension, including dimension zero. -/
theorem exists_coordinate_equiv_of_finrank (S : Submodule K (Fin n → K)) (hS : finrank K S = r) :
    ∃ j : Fin r ↪ Fin n, ∃ e : S ≃ₗ[K] (Fin r → K), ∀ x i, e x i = x.val (j i) := by
  subst r
  exact exists_coordinate_equiv S

/-- The unselected coordinates of a fixed chart. -/
abbrev Outside (j : Fin r ↪ Fin n) := {k : Fin n // k ∉ Set.range j}

/-- Exactly n-r ambient coordinates remain outside an injective selector. -/
theorem card_outside (j : Fin r ↪ Fin n) : Fintype.card (Outside j) = n-r := by
  classical
  simp only [Outside, Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin]

/-- Coefficients of the unselected coordinate linear forms. -/
abbrev Parameters (K : Type*) [Field K] (j : Fin r ↪ Fin n) := Outside j → Fin r → K

/-- Each fixed coordinate chart has precisely r(n-r) scalar coefficients. -/
theorem parameters_finrank (j : Fin r ↪ Fin n) : finrank K (Parameters K j) = r*(n-r) := by
  classical
  simp only [Parameters, Module.finrank_pi_fintype, finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [card_outside, mul_comm]

/-- The coefficient positions themselves form a set of cardinality r(n-r). -/
theorem card_coefficient_positions (j : Fin r ↪ Fin n) :
    Fintype.card (Outside j × Fin r) = r*(n-r) := by
  classical
  rw [Fintype.card_prod, card_outside, Fintype.card_fin, Nat.mul_comm]

/-- There are only finitely many coordinate selectors, hence finitely many chart types. -/
instance finite_selectors : Finite (Fin r ↪ Fin n) := inferInstance

/-- All ambient coordinates of the inverse chart are literal linear forms. -/
def coordinateForm {S : Submodule K (Fin n → K)} (e : S ≃ₗ[K] (Fin r → K)) (k : Fin n) :
    (Fin r → K) →ₗ[K] K := (LinearMap.proj k).comp (S.subtype.comp e.symm.toLinearMap)

@[simp] theorem coordinateForm_apply {S : Submodule K (Fin n → K)}
    (e : S ≃ₗ[K] (Fin r → K)) (k : Fin n) (u : Fin r → K) :
    coordinateForm e k u = (e.symm u).val k := rfl

/-- The chart coefficients are obtained by applying its inverse to the standard basis. -/
def coefficients {S : Submodule K (Fin n → K)} (j : Fin r ↪ Fin n)
    (e : S ≃ₗ[K] (Fin r → K)) : Parameters K j :=
  fun k i => coordinateForm e k.val (Pi.single i 1)

/-- Every linear coordinate form equals its explicit finite coefficient sum. -/
theorem coordinateForm_eq_sum {S : Submodule K (Fin n → K)}
    (e : S ≃ₗ[K] (Fin r → K)) (k : Fin n) (u : Fin r → K) :
    coordinateForm e k u = ∑ i, coordinateForm e k (Pi.single i 1)*u i := by
  have h := congrArg (coordinateForm e k) ((Pi.basisFun K (Fin r)).sum_equivFun u)
  simpa [Pi.basisFun_apply, Pi.basisFun_equivFun, map_sum, map_smul, smul_eq_mul, mul_comm] using h.symm

/-- Values of the selected coordinates determine every vector of the subspace. -/
theorem determined_by_coordinates {S : Submodule K (Fin n → K)} (j : Fin r ↪ Fin n)
    (e : S ≃ₗ[K] (Fin r → K)) (he : ∀ x i, e x i = x.val (j i))
    (x y : S) (h : ∀ i, x.val (j i) = y.val (j i)) : x=y := by
  apply e.injective
  funext i
  rw [he, he, h]

/-- Every unselected coordinate is the specified linear form in the selected coordinates. -/
theorem unselected_coordinate {S : Submodule K (Fin n → K)} (j : Fin r ↪ Fin n)
    (e : S ≃ₗ[K] (Fin r → K)) (he : ∀ x i, e x i = x.val (j i))
    (x : S) (k : Outside j) :
    x.val k.val = ∑ i, coefficients j e k i*x.val (j i) := by
  have h:=coordinateForm_eq_sum e k.val (e x)
  simpa only [coordinateForm_apply, LinearEquiv.symm_apply_apply, coefficients, he] using h

/-- The subspace is exactly the graph cut out by these coordinate formulas. -/
theorem mem_iff_graph {S : Submodule K (Fin n → K)} (j : Fin r ↪ Fin n)
    (e : S ≃ₗ[K] (Fin r → K)) (he : ∀ x i, e x i = x.val (j i)) (x : Fin n → K) :
    x ∈ S ↔ ∀ k : Outside j, x k.val = ∑ i, coefficients j e k i*x (j i) := by
  classical
  constructor
  · intro hx k
    exact unselected_coordinate j e he ⟨x,hx⟩ k
  · intro hx
    let y:S:=e.symm (fun i=>x (j i))
    have hy:∀i,y.val (j i)=x (j i):=by
      intro i
      rw [← he]
      exact congrFun (e.apply_symm_apply _) i
    have hxy:x=y.val:=by
      funext k
      by_cases hk:k ∈ Set.range j
      · obtain ⟨i,rfl⟩:=hk
        exact (hy i).symm
      · rw [hx ⟨k,hk⟩,unselected_coordinate j e he y ⟨k,hk⟩]
        simp only [hy]
    rw [hxy]
    exact y.property

/-- Projection onto the coordinates chosen by a fixed selector. -/
def selectedProjection (j : Fin r ↪ Fin n) : (Fin n → K) →ₗ[K] (Fin r → K) :=
  LinearMap.pi fun i => LinearMap.proj (j i)

/-- Projection onto the remaining ambient coordinates. -/
def outsideProjection (j : Fin r ↪ Fin n) : (Fin n → K) →ₗ[K] (Outside j → K) :=
  LinearMap.pi fun k => LinearMap.proj k.val

/-- The coefficient matrix as an actual linear map between coordinate spaces. -/
def parameterMap {j : Fin r ↪ Fin n} (A : Parameters K j) :
    (Fin r → K) →ₗ[K] (Outside j → K) :=
  LinearMap.pi fun k => ∑ i, A k i • LinearMap.proj i

@[simp] theorem parameterMap_apply {j : Fin r ↪ Fin n} (A : Parameters K j)
    (u : Fin r → K) (k : Outside j) : parameterMap A u k = ∑ i, A k i*u i := by
  simp [parameterMap]

/-- The subspace specified by one coordinate chart and its coefficient array. -/
def chartSubspace (j : Fin r ↪ Fin n) (A : Parameters K j) : Submodule K (Fin n → K) :=
  LinearMap.ker (outsideProjection j-(parameterMap A).comp (selectedProjection j))

@[simp] theorem mem_chartSubspace (j : Fin r ↪ Fin n) (A : Parameters K j) (x : Fin n → K) :
    x ∈ chartSubspace j A ↔ ∀ k : Outside j, x k.val=∑ i,A k i*x (j i) := by
  change outsideProjection j x-parameterMap A (selectedProjection j x)=0 ↔ _
  rw [sub_eq_zero,funext_iff]
  simp only [outsideProjection,selectedProjection,LinearMap.pi_apply,LinearMap.proj_apply,parameterMap_apply]

/-- The coefficient array reconstructs the original subspace exactly. -/
theorem chartSubspace_coefficients {S : Submodule K (Fin n → K)} (j : Fin r ↪ Fin n)
    (e : S ≃ₗ[K] (Fin r → K)) (he : ∀ x i, e x i=x.val (j i)) :
    chartSubspace j (coefficients j e)=S := by
  ext x
  rw [mem_chartSubspace,mem_iff_graph j e he]

/-- Every r-dimensional subspace belongs to one of the finitely many coordinate charts. -/
theorem exists_chart (S : Submodule K (Fin n → K)) (hS : finrank K S=r) :
    ∃ j : Fin r ↪ Fin n, ∃ A : Parameters K j, chartSubspace j A=S := by
  obtain ⟨j,e,he⟩:=exists_coordinate_equiv_of_finrank S hS
  exact ⟨j,coefficients j e,chartSubspace_coefficients j e he⟩

/-- Equality of the unselected-coordinate coefficients determines the subspace. -/
theorem coefficients_determine_subspace {S T : Submodule K (Fin n → K)} (j : Fin r ↪ Fin n)
    (e : S ≃ₗ[K] (Fin r → K)) (f : T ≃ₗ[K] (Fin r → K))
    (he : ∀ x i,e x i=x.val (j i)) (hf : ∀ x i,f x i=x.val (j i))
    (h : coefficients j e=coefficients j f) : S=T := by
  rw [← chartSubspace_coefficients j e he,← chartSubspace_coefficients j f hf,h]

/-- Fill the selected coordinates with u and the remaining coordinates with the chart's linear forms. -/
def chartLift (j : Fin r ↪ Fin n) (A : Parameters K j) :
    (Fin r → K) →ₗ[K] (Fin n → K) := by
  classical
  exact LinearMap.pi fun k => if hk:k ∈ Set.range j then LinearMap.proj (Classical.choose hk)
    else (LinearMap.proj ⟨k,hk⟩).comp (parameterMap A)

@[simp] theorem chartLift_selected (j : Fin r ↪ Fin n) (A : Parameters K j)
    (u : Fin r → K) (i : Fin r) : chartLift j A u (j i)=u i := by
  classical
  have h: j i ∈ Set.range j:=⟨i,rfl⟩
  have hi:Classical.choose h=i:=j.injective (Classical.choose_spec h)
  simp only [chartLift,LinearMap.pi_apply,dite_eq_left h,LinearMap.proj_apply,hi]

@[simp] theorem chartLift_outside (j : Fin r ↪ Fin n) (A : Parameters K j)
    (u : Fin r → K) (k : Outside j) : chartLift j A u k.val=parameterMap A u k := by
  classical
  simp only [chartLift,LinearMap.pi_apply,dite_eq_right k.property,LinearMap.comp_apply,LinearMap.proj_apply]

 theorem chartLift_mem (j : Fin r ↪ Fin n) (A : Parameters K j) (u : Fin r → K) :
    chartLift j A u ∈ chartSubspace j A := by
  rw [mem_chartSubspace]
  intro k
  simp only [chartLift_outside,parameterMap_apply,chartLift_selected]

/-- Every coefficient array defines an r-dimensional graph, with precisely the selected coordinates. -/
def chartEquiv (j : Fin r ↪ Fin n) (A : Parameters K j) :
    chartSubspace j A ≃ₗ[K] (Fin r → K) where
  toFun x:=selectedProjection j x.val
  invFun u:=⟨chartLift j A u,chartLift_mem j A u⟩
  left_inv x:=by
    classical
    apply Subtype.ext
    funext k
    change chartLift j A (selectedProjection j x.val) k=x.val k
    by_cases hk:k ∈ Set.range j
    · obtain ⟨i,rfl⟩:=hk
      exact chartLift_selected j A _ i
    · rw [chartLift_outside j A _ ⟨k,hk⟩,parameterMap_apply]
      exact ((mem_chartSubspace j A x.val).mp x.property ⟨k,hk⟩).symm
  right_inv u:=by
    funext i
    exact chartLift_selected j A u i
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

@[simp] theorem chartEquiv_apply (j : Fin r ↪ Fin n) (A : Parameters K j)
    (x : chartSubspace j A) (i : Fin r) : chartEquiv j A x i=x.val (j i) := rfl

 theorem chartSubspace_finrank (j : Fin r ↪ Fin n) (A : Parameters K j) :
    finrank K (chartSubspace j A)=r := by
  rw [(chartEquiv j A).finrank_eq]
  simp

/-- Two arrays in the same chart define the same subspace only when all their coefficients agree. -/
theorem chartSubspace_injective (j : Fin r ↪ Fin n) :
    Function.Injective (chartSubspace (K := K) j) := by
  intro A B h
  funext k i
  have hm:=chartLift_mem j A (Pi.single i 1)
  rw [h,mem_chartSubspace] at hm
  have hk:=hm k
  simp only [chartLift_outside,parameterMap_apply,chartLift_selected] at hk
  simpa [Pi.single_apply, eq_comm] using hk

end Quartic.SubspaceCharts
