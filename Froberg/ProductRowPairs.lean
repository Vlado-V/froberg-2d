module

public import Froberg.ProductRows

@[expose] public section

/-! Canonical unordered generator pairs behind the product-row source. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial

abbrev LayerLabel (J : Finset ℕ) (e : ℕ → ℕ) := (j : J) × Fin (e j.val)

def layerLabel {J : Finset ℕ} (e : ℕ → ℕ) (j : ℕ) (hj : j∈J) (i : Fin (e j)) :
    LayerLabel J e := ⟨⟨j,hj⟩,i⟩

theorem layerLabel_injective {J : Finset ℕ} (e : ℕ → ℕ) (j : ℕ) (hj : j∈J) :
    Function.Injective (layerLabel e j hj) := by
  intro i k h
  cases h
  rfl

/-- The literal unordered generator pair represented by one product column. -/
def rowPair {J : Finset ℕ} (e : ℕ → ℕ) {R : ℕ} (r : Row J R) :
    Columns e r → Sym2 (LayerLabel J e) :=
  if h : r.val.val=R-r.val.val then fun c =>
    Sym2.map (layerLabel e r.val.val r.property.1) (cast (if_pos h) c)
  else fun c =>
    let p : Fin (e r.val.val) × Fin (e (R-r.val.val)) := cast (if_neg h) c
    s(layerLabel e r.val.val r.property.1 p.1,
      layerLabel e (R-r.val.val) r.property.2.1 p.2)

def pairMinimum {J : Finset ℕ} {e : ℕ → ℕ} : Sym2 (LayerLabel J e) → ℕ :=
  Sym2.lift ⟨fun a b => min a.1.val b.1.val,fun a b => min_comm _ _⟩

def pairDegree {J : Finset ℕ} {e : ℕ → ℕ} : Sym2 (LayerLabel J e) → ℕ :=
  Sym2.lift ⟨fun a b => a.1.val+b.1.val,fun a b => add_comm _ _⟩

theorem rowPair_minimum {J : Finset ℕ} (e : ℕ → ℕ) {R : ℕ}
    (r : Row J R) (c : Columns e r) : pairMinimum (rowPair e r c)=r.val.val := by
  classical
  by_cases h : r.val.val=R-r.val.val
  · unfold rowPair
    simp only [dif_pos h]
    generalize hc : cast (if_pos h) c=p
    induction p using Sym2.inductionOn with
    | _ i k => simp [pairMinimum,layerLabel]
  · unfold rowPair
    simp only [dif_neg h,pairMinimum,Sym2.lift_mk,layerLabel]
    apply min_eq_left
    have hh := r.property.2.2
    omega

theorem rowPair_degree {J : Finset ℕ} (e : ℕ → ℕ) {R : ℕ}
    (r : Row J R) (c : Columns e r) : pairDegree (rowPair e r c)=R := by
  classical
  have hr := r.property.2.2
  by_cases h : r.val.val=R-r.val.val
  · unfold rowPair
    simp only [dif_pos h]
    generalize hc : cast (if_pos h) c=p
    induction p using Sym2.inductionOn with
    | _ i k => simp only [Sym2.map_mk,pairDegree,Sym2.lift_mk,layerLabel]; omega
  · unfold rowPair
    simp only [dif_neg h,pairDegree,Sym2.lift_mk,layerLabel]
    omega

theorem rowPair_injective {J : Finset ℕ} (e : ℕ → ℕ) {R : ℕ} (r : Row J R) :
    Function.Injective (rowPair e r) := by
  classical
  intro c c' hcc
  by_cases h : r.val.val=R-r.val.val
  · simp only [rowPair,dif_pos h] at hcc
    have hp := Sym2.map.injective (layerLabel_injective e r.val.val r.property.1) hcc
    exact (Equiv.cast (if_pos h)).injective hp
  · simp only [rowPair,dif_neg h] at hcc
    rcases Sym2.eq_iff.mp hcc with hd|hs
    · apply (Equiv.cast (if_neg h)).injective
      exact Prod.ext ((layerLabel_injective e _ _) hd.1) ((layerLabel_injective e _ _) hd.2)
    · have hx := congrArg (fun a : LayerLabel J e => a.1.val) hs.1
      exact False.elim (h hx)

/-- No two distinct product columns represent the same unordered pair. -/
theorem allRowPairs_injective {J : Finset ℕ} (e : ℕ → ℕ) (R : ℕ) :
    Function.Injective (fun p : (r : Row J R) × Columns e r => rowPair e p.1 p.2) := by
  intro p q hpq
  have hr : p.1=q.1 := by
    apply Subtype.ext
    apply Fin.ext
    have h := congrArg pairMinimum hpq
    simpa only [rowPair_minimum] using h
  rcases p with ⟨r,c⟩
  rcases q with ⟨r',c'⟩
  dsimp at hr
  subst r'
  exact congrArg (Sigma.mk r) (rowPair_injective e r hpq)

/-- Every ordered pair of layers in increasing order gives a product column. -/
theorem exists_rowPair_of_le {J : Finset ℕ} (e : ℕ → ℕ)
    (j k : ℕ) (hj : j∈J) (hk : k∈J) (hjk : j≤k)
    (i : Fin (e j)) (l : Fin (e k)) :
    ∃ p : (r : Row J (j+k)) × Columns e r,
      rowPair e p.1 p.2=s(layerLabel e j hj i,layerLabel e k hk l) := by
  classical
  let r : Row J (j+k) := ⟨⟨j,by omega⟩,hj,by simpa using hk,by change 2*j≤j+k; omega⟩
  have hrj : r.val.val=j := rfl
  have hrk : j+k-r.val.val=k := by dsimp [r]; omega
  by_cases heq : j=k
  · subst k
    have hd : r.val.val=j+j-r.val.val := by dsimp [r]; omega
    let c : Columns e r := (Equiv.cast (if_pos hd)).symm s(i,l)
    refine ⟨⟨r,c⟩,?_⟩
    have hc : cast (if_pos hd) c=s(i,l) := (Equiv.cast (if_pos hd)).apply_symm_apply _
    rw [rowPair,dif_pos hd,hc]
    rfl
  · have hd : r.val.val≠j+k-r.val.val := by rw [hrj,hrk]; exact heq
    let l' : Fin (e (j+k-r.val.val)) := Fin.cast (congrArg e hrk.symm) l
    let c : Columns e r := (Equiv.cast (if_neg hd)).symm (i,l')
    refine ⟨⟨r,c⟩,?_⟩
    have hc : cast (if_neg hd) c=(i,l') := (Equiv.cast (if_neg hd)).apply_symm_apply _
    rw [rowPair,dif_neg hd,hc]
    apply congrArg (fun b => s(layerLabel e j hj i,b))
    apply Sigma.ext (Subtype.ext hrk)
    exact (Fin.heq_ext_iff (congrArg e hrk)).mpr rfl

/-- Every unordered pair of the required total degree occurs in the source. -/
theorem exists_rowPair {J : Finset ℕ} (e : ℕ → ℕ) {R : ℕ}
    (p : Sym2 (LayerLabel J e)) (hp : pairDegree p=R) :
    ∃ a : (r : Row J R) × Columns e r,rowPair e a.1 a.2=p := by
  induction p using Sym2.inductionOn with
  | _ a b =>
    rcases a with ⟨⟨j,hj⟩,i⟩
    rcases b with ⟨⟨k,hk⟩,l⟩
    change j+k=R at hp
    subst R
    rcases le_total j k with hle|hle
    · exact exists_rowPair_of_le e j k hj hk hle i l
    · have h := exists_rowPair_of_le e k j hk hj hle l i
      rw [add_comm k j] at h
      obtain ⟨p,hp⟩ := h
      exact ⟨p,hp.trans (Sym2.eq_swap ..)⟩

theorem products_eq_pairProducts {K : Type} {σ : Type*} [Field K]
    {J : Finset ℕ} (e : ℕ → ℕ) (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    {R : ℕ} (r : Row J R) (c : Columns e r) :
    products e q r c=pairProducts (fun a : LayerLabel J e => q a.1.val a.2) (rowPair e r c) := by
  classical
  by_cases h : r.val.val=R-r.val.val
  · simp only [products,rowPair,dif_pos h]
    generalize hc : cast (if_pos h) c=p
    induction p using Sym2.inductionOn with
    | _ i k => rfl
  · simp only [products,rowPair,dif_neg h]
    rfl

/-- Product columns and unordered pairs of the prescribed degree are exactly

the same finite source. -/
def rowPairEquiv {J : Finset ℕ} (e : ℕ → ℕ) (R : ℕ) :
    ((r : Row J R) × Columns e r) ≃ {p : Sym2 (LayerLabel J e) // pairDegree p=R} :=
  Equiv.ofBijective (fun p => ⟨rowPair e p.1 p.2,rowPair_degree e p.1 p.2⟩)
    ⟨fun _ _ h => allRowPairs_injective e R (congrArg Subtype.val h),by
      intro p
      obtain ⟨a,ha⟩ := exists_rowPair e p.val p.property
      exact ⟨a,Subtype.ext ha⟩⟩

theorem linearIndependent_degree_pairs {K : Type} {σ : Type*} [Field K]
    {J : Finset ℕ} (e : ℕ → ℕ) (R : ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (hq : Function.Injective (multiplication e q J R)) :
    LinearIndependent K (fun p : {p : Sym2 (LayerLabel J e) // pairDegree p=R} =>
      pairProducts (fun a : LayerLabel J e => q a.1.val a.2) p.val) := by
  have h : LinearIndependent K (fun p : (r : Row J R) × Columns e r => products e q p.1 p.2) := hq
  have h' := h.comp (rowPairEquiv e R).symm (rowPairEquiv e R).symm.injective
  convert h' using 1
  funext p
  rw [Function.comp_apply,products_eq_pairProducts]
  have heq := congrArg Subtype.val ((rowPairEquiv e R).apply_symm_apply p)
  exact congrArg (pairProducts (fun a : LayerLabel J e => q a.1.val a.2)) heq.symm

end Froberg.ProductRows
