module

public import Quartic.BlockSubspaceCharts
public import Quartic.FilteredImage

@[expose] public section

/-!
# Selected coordinates adapted to an actual prefix filtration

Selectors on each initial piece jointly give a coordinate equivalence on the
original subspace. Its inverse preserves prefixes. These statements supply
the coverage argument for the finite triangular block charts.
-/

noncomputable section
namespace Quartic.IteratedBlockCharts
open Module SubspaceCharts FilteredImage
variable {K : Type*} [Field K] {n : ℕ} {b r : Fin n → ℕ}

abbrev Ambient (K : Type*) (b : Fin n → ℕ) := (i : Fin n) → Fin (b i) → K
abbrev Selectors (b r : Fin n → ℕ) := (i : Fin n) → Fin (r i) ↪ Fin (b i)

/-- Joint projection onto the coordinates chosen in every block. -/
def selected (j : Selectors b r) : Ambient K b →ₗ[K] Ambient K r :=
  LinearMap.piMap fun i => selectedProjection (j i)

@[simp] theorem selected_apply (j : Selectors b r) (x : Ambient K b)
    (i : Fin n) (a : Fin (r i)) : selected j x i a=x i (j i a) := rfl

/-- The selected coordinates distinguish every vector in each actual initial piece. -/
def Separates (S : Submodule K (Ambient K b)) (j : Selectors b r) : Prop :=
  ∀ i, ∀ x ∈ initialPiece (fun i => Fin (b i) → K) S i,
    selectedProjection (j i) x=0 → x=0

theorem exists_separating_selectors (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i) :
    ∃ j : Selectors b r, Separates S j := by
  classical
  choose j e he using fun i => exists_coordinate_equiv_of_finrank
    (initialPiece (fun i => Fin (b i) → K) S i) (hr i)
  refine ⟨j,fun i x hx hzero => ?_⟩
  have hezero : e i ⟨x,hx⟩=0 := by
    funext a
    rw [he]
    exact congrFun hzero a
  have hsub : (⟨x,hx⟩ : initialPiece (fun i => Fin (b i) → K) S i)=0 :=
    (e i).injective (hezero.trans (map_zero (e i)).symm)
  exact congrArg Subtype.val hsub

/-- Vanishing of all selected coordinates after a prefix forces the actual
vector to be supported in that prefix. -/
theorem selected_reflects_prefix (S : Submodule K (Ambient K b))
    (j : Selectors b r) (hj : Separates S j) (k : ℕ) (x : Ambient K b)
    (hx : x ∈ S) (hsel : ∀ i : Fin n,k ≤ i.val → selected j x i=0) :
    x ∈ coordinateFlag (K := K) (fun i => Fin (b i) → K) k := by
  have step : ∀ m : ℕ,m ≤ n → k ≤ m →
      x ∈ coordinateFlag (K := K) (fun i => Fin (b i) → K) m →
      x ∈ coordinateFlag (K := K) (fun i => Fin (b i) → K) k := by
    intro m
    induction m with
    | zero =>
      intro _ hk hflag
      have : k=0 := Nat.eq_zero_of_le_zero hk
      simpa only [this] using hflag
    | succ m ih =>
      intro hm hk hflag
      by_cases hkm:k=m+1
      · simpa only [hkm] using hflag
      have hkm' : k ≤ m := by omega
      let i : Fin n := ⟨m,by omega⟩
      have hmem : x i ∈ initialPiece (fun i => Fin (b i) → K) S i :=
        ⟨x,⟨hx,hflag⟩,rfl⟩
      have hxi : x i=0 := hj i (x i) hmem (hsel i hkm')
      apply ih (by omega) hkm'
      intro l hl
      by_cases hli:l.val=m
      · have hli' : l=i := Fin.ext hli
        subst l
        exact hxi
      · exact hflag l (by omega)
  by_cases hkn:k ≤ n
  · exact step n le_rfl hkn (by rw [coordinateFlag_end]; exact Submodule.mem_top)
  · intro i hi
    exact False.elim (by omega)

/-- The joint selected-coordinate map on the actual subspace. -/
def selectedOn (S : Submodule K (Ambient K b)) (j : Selectors b r) :
    S →ₗ[K] Ambient K r := (selected j).comp S.subtype

theorem selectedOn_injective (S : Submodule K (Ambient K b))
    (j : Selectors b r) (hj : Separates S j) : Function.Injective (selectedOn S j) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hflag := selected_reflects_prefix S j hj 0 x.val x.property
    (fun i _ => congrFun hx i)
  rw [coordinateFlag_zero] at hflag
  exact Subtype.ext hflag

theorem selectedOn_surjective (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) : Function.Surjective (selectedOn S j) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj (selectedOn_injective S j hj)]
  rw [← sum_initialPiece_finrank (fun i => Fin (b i) → K) S]
  simp [hr,Ambient,Module.finrank_pi_fintype]

/-- An actual equivalence between the subspace and all its selected coordinates. -/
def selectedEquiv (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) : S ≃ₗ[K] Ambient K r :=
  LinearEquiv.ofBijective (selectedOn S j)
    ⟨selectedOn_injective S j hj,selectedOn_surjective S hr j hj⟩

@[simp] theorem selectedEquiv_apply (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) (x : S) :
    selectedEquiv S hr j hj x=selected j x.val := rfl

/-- The inverse coordinate map preserves the same ordered prefixes. -/
theorem selectedEquiv_symm_prefix (S : Submodule K (Ambient K b))
    (hr : ∀ i,finrank K (initialPiece (fun i => Fin (b i) → K) S i)=r i)
    (j : Selectors b r) (hj : Separates S j) (k : ℕ) (y : Ambient K r)
    (hy : y ∈ coordinateFlag (K := K) (fun i => Fin (r i) → K) k) :
    ((selectedEquiv S hr j hj).symm y).val ∈
      coordinateFlag (K := K) (fun i => Fin (b i) → K) k := by
  apply selected_reflects_prefix S j hj k _ ((selectedEquiv S hr j hj).symm y).property
  intro i hi
  have h := congrFun ((selectedEquiv S hr j hj).apply_symm_apply y) i
  exact h.trans (hy i hi)

end Quartic.IteratedBlockCharts
