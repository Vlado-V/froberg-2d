import Quartic.IteratedBlockCharts.Selectors

/-!
# Finite triangular polynomial charts adapted to ordered blocks

Outside coordinates in block i depend only on selected coordinates in blocks
j ≥ i. This is the last-leading convention of the actual prefix filtration.
The complement coordinates are the same explicit fillers used in the
two-block chart construction.
-/

noncomputable section
namespace Quartic.IteratedBlockCharts
open Module SubspaceCharts FilteredImage
variable {K : Type*} [Field K] {n : ℕ} {b r : Fin n → ℕ}

/-- One scalar for each outside row and selected column at or after its block. -/
abbrev ParameterIndex (j : Selectors b r) :=
  (i : Fin n) × Outside (j i) × (l : {l : Fin n // i ≤ l}) × Fin (r l.val)

abbrev Parameters (K : Type*) (j : Selectors b r) := ParameterIndex j → K

/-- All outside coordinates in one block, as linear forms in selected coordinates. -/
def tailMap (j : Selectors b r) (p : Parameters K j) (i : Fin n) :
    Ambient K r →ₗ[K] (Outside (j i) → K) := by
  classical
  exact LinearMap.pi fun k => ∑ l : Fin n, if h:i ≤ l then
    ∑ a : Fin (r l),p ⟨i,k,⟨l,h⟩,a⟩ •
      (LinearMap.proj a : (Fin (r l) → K) →ₗ[K] K).comp
        (LinearMap.proj l : Ambient K r →ₗ[K] (Fin (r l) → K))
    else 0

@[simp] theorem tailMap_apply (j : Selectors b r) (p : Parameters K j)
    (i : Fin n) (x : Ambient K r) (k : Outside (j i)) :
    tailMap j p i x k=∑ l : Fin n,if h:i ≤ l then
      ∑ a : Fin (r l),p ⟨i,k,⟨l,h⟩,a⟩*x l a else 0 := by
  classical
  simp only [tailMap,LinearMap.pi_apply,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

/-- Fill the selected coordinates and their triangular outside-coordinate forms. -/
def lift (j : Selectors b r) (p : Parameters K j) : Ambient K r →ₗ[K] Ambient K b :=
  LinearMap.pi fun i => ((chartLift (j i) 0).comp (LinearMap.proj i))+
    (BlockSubspaceCharts.outsideLift (j i)).comp (tailMap j p i)

@[simp] theorem lift_selected (j : Selectors b r) (p : Parameters K j)
    (x : Ambient K r) (i : Fin n) (a : Fin (r i)) : lift j p x i (j i a)=x i a := by
  simp [lift]

@[simp] theorem lift_outside (j : Selectors b r) (p : Parameters K j)
    (x : Ambient K r) (i : Fin n) (k : Outside (j i)) :
    lift j p x i k.val=tailMap j p i x k := by
  simp [lift,chartLift_outside,parameterMap_apply,BlockSubspaceCharts.outsideLift_outside]

@[simp] theorem selected_lift (j : Selectors b r) (p : Parameters K j)
    (x : Ambient K r) : selected j (lift j p x)=x := by
  funext i a
  exact lift_selected j p x i a

theorem lift_injective (j : Selectors b r) (p : Parameters K j) :
    Function.Injective (lift j p) := by
  intro x y h
  simpa only [selected_lift] using congrArg (selected j) h

def chart (j : Selectors b r) (p : Parameters K j) : Submodule K (Ambient K b) :=
  LinearMap.range (lift j p)

theorem chart_finrank (j : Selectors b r) (p : Parameters K j) :
    finrank K (chart j p)=∑ i,r i := by
  rw [chart,LinearMap.finrank_range_of_inj (lift_injective j p)]
  simp [Ambient,Module.finrank_pi_fintype]

/-- The triangular lift preserves every prefix of selected blocks. -/
theorem lift_prefix (j : Selectors b r) (p : Parameters K j) (k : ℕ)
    (x : Ambient K r) (hx : x ∈ coordinateFlag (K := K) (fun i => Fin (r i) → K) k) :
    lift j p x ∈ coordinateFlag (K := K) (fun i => Fin (b i) → K) k := by
  classical
  intro i hi
  funext a
  by_cases ha:a ∈ Set.range (j i)
  · obtain ⟨l,rfl⟩ := ha
    rw [lift_selected,hx i hi]
    rfl
  · rw [show a=(⟨a,ha⟩ : Outside (j i)).val from rfl,lift_outside,tailMap_apply]
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with hil
    · rw [hx l (hi.trans hil)]
      simp
    · rfl

/-- The diagonal part is a usual coordinate chart on the corresponding initial piece. -/
def diagonal (j : Selectors b r) (p : Parameters K j) (i : Fin n) :
    SubspaceCharts.Parameters K (j i) := fun k a => p ⟨i,k,⟨i,le_rfl⟩,a⟩

theorem tailMap_on_prefix (j : Selectors b r) (p : Parameters K j) (i : Fin n)
    (x : Ambient K r)
    (hx : x ∈ coordinateFlag (K := K) (fun i => Fin (r i) → K) (i.val+1)) :
    tailMap j p i x=parameterMap (diagonal j p i) (x i) := by
  classical
  funext k
  rw [tailMap_apply,parameterMap_apply]
  rw [Finset.sum_eq_single i]
  · simp [diagonal]
  · intro l _ hli
    split_ifs with hil
    · rw [hx l (by have hne : l.val ≠ i.val := fun h => hli (Fin.ext h); omega)]
      simp
    · rfl
  · simp

theorem lift_on_prefix (j : Selectors b r) (p : Parameters K j) (i : Fin n)
    (x : Ambient K r)
    (hx : x ∈ coordinateFlag (K := K) (fun i => Fin (r i) → K) (i.val+1)) :
    lift j p x i=chartLift (j i) (diagonal j p i) (x i) := by
  classical
  funext a
  by_cases ha:a ∈ Set.range (j i)
  · obtain ⟨l,rfl⟩ := ha
    rw [lift_selected,chartLift_selected]
  · rw [show a=(⟨a,ha⟩ : Outside (j i)).val from rfl,lift_outside,chartLift_outside,
      tailMap_on_prefix j p i x hx]

/-- The actual initial pieces of the chart are exactly its diagonal charts. -/
theorem initialPiece_chart (j : Selectors b r) (p : Parameters K j) (i : Fin n) :
    initialPiece (fun i => Fin (b i) → K) (chart j p) i=
      chartSubspace (j i) (diagonal j p i) := by
  classical
  apply le_antisymm
  · rintro _ ⟨z,⟨⟨x,rfl⟩,hprefix⟩,rfl⟩
    have hx : x ∈ coordinateFlag (K := K) (fun i => Fin (r i) → K) (i.val+1) := by
      intro l hl
      funext a
      have hz := congrFun (hprefix l hl) (j l a)
      simpa only [lift_selected,Pi.zero_apply] using hz
    change lift j p x i ∈ _
    rw [lift_on_prefix j p i x hx]
    exact chartLift_mem _ _ _
  · intro y hy
    let x : Ambient K r := Pi.single i (selectedProjection (j i) y)
    have hx : x ∈ coordinateFlag (K := K) (fun i => Fin (r i) → K) (i.val+1) := by
      intro l hl
      have hli : l ≠ i := by intro h; subst l; omega
      simp [x,Pi.single_eq_of_ne hli]
    refine ⟨lift j p x,⟨⟨x,rfl⟩,lift_prefix j p _ x hx⟩,?_⟩
    change lift j p x i=y
    rw [lift_on_prefix j p i x hx]
    simpa [x] using BlockSubspaceCharts.chartLift_selected_of_mem (j i) (diagonal j p i) hy

theorem initialPiece_chart_finrank (j : Selectors b r) (p : Parameters K j) (i : Fin n) :
    finrank K (initialPiece (fun i => Fin (b i) → K) (chart j p) i)=r i := by
  rw [initialPiece_chart,chartSubspace_finrank]

/-- A standard selected-coordinate vector in a single block. -/
def basisVector (i : Fin n) (a : Fin (r i)) : Ambient K r := Pi.single i (Pi.single a 1)

theorem basisVector_prefix (i : Fin n) (a : Fin (r i)) :
    basisVector (K := K) i a ∈
      coordinateFlag (K := K) (fun i => Fin (r i) → K) (i.val+1) := by
  classical
  intro l hl
  have hli : l ≠ i := by intro h; subst l; omega
  simp [basisVector,Pi.single_eq_of_ne hli]

theorem coordinate_expansion (x : Ambient K r) :
    x=∑ i : Fin n,∑ a : Fin (r i),x i a • basisVector i a := by
  classical
  funext i a
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  symm
  rw [Finset.sum_eq_single i]
  · simp [basisVector,Pi.single_apply]
  · intro l _ hli
    apply Finset.sum_eq_zero
    intro c _
    simp [basisVector,Pi.single_eq_of_ne hli.symm]
  · simp

/-- The actual inverse of the joint selected coordinates, viewed in the ambient space. -/
def inverseLift (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) : Ambient K r →ₗ[K] Ambient K b :=
  S.subtype.comp (selectedEquiv S hr j hj).symm.toLinearMap

@[simp] theorem selected_inverseLift (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) (x : Ambient K r) :
    selected j (inverseLift S hr j hj x)=x :=
  (selectedEquiv S hr j hj).apply_symm_apply x

theorem inverseLift_basis_eq_zero (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j)
    (l : Fin n) (a : Fin (r l)) (i : Fin n) (hli : l < i) :
    inverseLift S hr j hj (basisVector l a) i=0 :=
  selectedEquiv_symm_prefix S hr j hj (l.val+1) _ (basisVector_prefix l a) i hli

/-- The triangular coefficients of an actual subspace are read from its inverse coordinates. -/
def coefficients (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) : Parameters K j :=
  fun ⟨i,k,l,a⟩ => inverseLift S hr j hj (basisVector l.val a) i k.val

/-- The polynomial chart lift is the actual inverse coordinate map. -/
theorem lift_coefficients (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) :
    lift j (coefficients S hr j hj)=inverseLift S hr j hj := by
  classical
  apply LinearMap.ext
  intro x
  funext i k
  by_cases hk:k ∈ Set.range (j i)
  · obtain ⟨a,rfl⟩ := hk
    rw [lift_selected]
    exact (congrFun (congrFun (selected_inverseLift S hr j hj x) i) a).symm
  · rw [show k=(⟨k,hk⟩ : Outside (j i)).val from rfl,lift_outside,tailMap_apply]
    conv_rhs => rw [coordinate_expansion x]
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hil:i ≤ l
    · rw [dite_eq_left hil]
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    · rw [dite_eq_right hil]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro a _
      rw [inverseLift_basis_eq_zero S hr j hj l a i (lt_of_not_ge hil)]
      simp

/-- The reconstructed chart equals the original subspace, not merely a model of its dimensions. -/
theorem chart_coefficients (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) : chart j (coefficients S hr j hj)=S := by
  rw [chart,lift_coefficients,inverseLift,LinearMap.range_comp_of_range_eq_top _
    (selectedEquiv S hr j hj).symm.range,Submodule.range_subtype]

/-- Every subspace with prescribed prefix ranks belongs to a finite triangular chart. -/
theorem exists_chart (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i) :
    ∃ j : Selectors b r,∃ p : Parameters K j,chart j p=S := by
  obtain ⟨j,hj⟩ := exists_separating_selectors S hr
  exact ⟨j,coefficients S hr j hj,chart_coefficients S hr j hj⟩

instance finite_selectors : Finite (Selectors b r) := inferInstance

/-- Dimension of a profile chart in the last-leading prefix convention. -/
def parameterCount (b r : Fin n → ℕ) : ℕ :=
  (∑ i,r i*(b i-r i))+(∑ i,∑ l : Fin n,if i < l then r l*(b i-r i) else 0)

theorem tail_rank_sum (r : Fin n → ℕ) (i : Fin n) :
    (∑ l : {l : Fin n // i ≤ l},r l.val)=
      r i+∑ l : Fin n,if i < l then r l else 0 := by
  classical
  have hsub := Finset.sum_subtype (p := fun l : Fin n => i ≤ l) (F := inferInstance)
    (Finset.univ.filter fun l : Fin n => i ≤ l)
    (by intro l; simp) r
  rw [← hsub,Finset.sum_filter]
  calc
    (∑ l : Fin n,if i ≤ l then r l else 0)=
        ∑ l : Fin n,((if l=i then r i else 0)+(if i < l then r l else 0)) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hli:l=i
      · subst l; simp
      · by_cases hil:i < l
        · simp [hli,hil,le_of_lt hil]
        · have hnot : ¬i ≤ l := by intro h; exact hli (le_antisymm (le_of_not_gt hil) h)
          simp [hli,hil,hnot]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- Cardinality of the literal coefficient positions equals the profile expression. -/
theorem parameter_count (j : Selectors b r) :
    Fintype.card (ParameterIndex j)=parameterCount b r := by
  classical
  simp only [ParameterIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,card_outside]
  rw [parameterCount,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [tail_rank_sum,Nat.mul_add,Finset.mul_sum]
  congr 1
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp [mul_comm]

theorem parameters_finrank (j : Selectors b r) :
    finrank K (Parameters K j)=parameterCount b r := by
  classical
  change finrank K (ParameterIndex j → K)=_
  rw [Module.finrank_fintype_fun_eq_card,parameter_count]

/-- Literal polynomial coordinates of any chart basis combination. -/
def liftPolynomial (j : Selectors b r) (x : Ambient K r)
    (i : Fin n) (k : Fin (b i)) : MvPolynomial (ParameterIndex j) K := by
  classical
  exact if h:k ∈ Set.range (j i) then MvPolynomial.C (x i (Classical.choose h)) else
    ∑ l : Fin n,if hil:i ≤ l then
      ∑ a : Fin (r l),MvPolynomial.X ⟨i,⟨k,h⟩,⟨l,hil⟩,a⟩*MvPolynomial.C (x l a)
      else 0

/-- Polynomial evaluation is exactly the actual triangular lift. -/
theorem eval_liftPolynomial (j : Selectors b r) (p : Parameters K j)
    (x : Ambient K r) (i : Fin n) (k : Fin (b i)) :
    MvPolynomial.eval p (liftPolynomial j x i k)=lift j p x i k := by
  classical
  by_cases hk:k ∈ Set.range (j i)
  · obtain ⟨a,rfl⟩ := hk
    have h : j i a ∈ Set.range (j i) := ⟨a,rfl⟩
    have he : Classical.choose h=a := (j i).injective (Classical.choose_spec h)
    simp only [liftPolynomial,dite_eq_left h,MvPolynomial.eval_C,he,lift_selected]
  · rw [show k=(⟨k,hk⟩ : Outside (j i)).val from rfl,lift_outside,tailMap_apply]
    simp only [liftPolynomial,dite_eq_right hk,map_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> simp

end Quartic.IteratedBlockCharts
