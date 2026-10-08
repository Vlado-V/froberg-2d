import Froberg.OddScalarLayerGrowth

/-! One common scalar/linear parameter open gives the required growth in
every non-top odd layer at once. Auxiliary scalar families are not added
to the actual generator count. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Froberg
open Module TensorProduct MvPolynomial Filter
open scoped Topology
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K] [Infinite K]

abbrev OddLayerParameters (K : Type*) [Field K] (h n d qO qS : ℕ) :=
  (Fin qO → Forms K h 1 ⊗[K] Forms K n (d-1)) ×
  (Fin qS → Forms K h 0 ⊗[K] Forms K n d)

def OddLayerCount (h n d qS qO t b : ℕ) : Prop :=
  (qS+t+(h+b-1).choose b*(n+(d-b)-1).choose (d-b))*
    ((h+b-1).choose b*(n+(d-b)-1).choose (d-b))+
  (qO+(h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1))*
    ((h+(b-1)-1).choose (b-1)*(n+(d-b+1)-1).choose (d-b+1)) ≤
  (h+b-1).choose b*(n+(2*d-b)-1).choose (2*d-b)

def OddScalarLayerProperty {h n d qO qS b : ℕ} (t : ℕ) (hb : 1≤b) (hbd : b≤d)
    (p : OddLayerParameters K h n d qO qS) : Prop :=
  Function.Injective (twoFamilyMultiplication (K := K)
      (P₁ := Forms K h 1 ⊗[K] Forms K n (d-1))
      (P₂ := Forms K h 0 ⊗[K] Forms K n d)
      (V₁ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
      (V₂ := Forms K h b ⊗[K] Forms K n (d-b))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
    (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) (oddRowScalarAction (K := K) (h := h) (n := n) hbd) p) ∧
  ∀ L : Submodule K (Forms K h b ⊗[K] Forms K n (d-b)),
    t*finrank K L ≤ finrank K (Quartic.BilinearImage.image
      (scalarModulo (K := K)
      (P := Forms K h 0 ⊗[K] Forms K n d)
      (V := Forms K h b ⊗[K] Forms K n (d-b))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
      (U := (Fin qO → Forms K h (b-1) ⊗[K] Forms K n (d-b+1)) ×
        (Fin qS → Forms K h b ⊗[K] Forms K n (d-b)))
      (twoFamilyMultiplication (K := K)
      (P₁ := Forms K h 1 ⊗[K] Forms K n (d-1))
      (P₂ := Forms K h 0 ⊗[K] Forms K n d)
      (V₁ := Forms K h (b-1) ⊗[K] Forms K n (d-b+1))
      (V₂ := Forms K h b ⊗[K] Forms K n (d-b))
      (W := Forms K h b ⊗[K] Forms K n (2*d-b))
        (oddRowLinearAction (K := K) (h := h) (n := n) hb hbd) (oddRowScalarAction (K := K) (h := h) (n := n) hbd) p)
        (oddRowScalarAction (K := K) (h := h) (n := n) hbd)) L)

def HasOddScalarLayersOpen (K : Type*) [Field K] (h n d qO qS t : ℕ) : Prop :=
  ∃ D : MvPolynomial (Fin (finrank K (OddLayerParameters K h n d qO qS))) K,
    (∃ p : OddLayerParameters K h n d qO qS,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
    ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
      ∀ (b : ℕ) (hb : 3≤b) (hbd : b≤d),OddScalarLayerProperty t (by omega) hbd p

theorem odd_scalar_layers_open {h n d qO qS t : ℕ}
    (hh : 0<h) (hn : 0<n)
    (hcount : ∀ b,3≤b → b≤d → OddLayerCount h n d qS qO t b) :
    HasOddScalarLayersOpen K h n d qO qS t := by
  classical
  let I := {b : Fin (d+1) // 3≤b.val}
  have hi (b : I) : ∃ D : MvPolynomial (Fin (finrank K (OddLayerParameters K h n d qO qS))) K,
      (∃ p : OddLayerParameters K h n d qO qS,eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p,eval ((Module.finBasis K _).equivFun p) D≠0 →
        OddScalarLayerProperty t (b := b.val.val) (by have := b.property; omega)
          (by have := b.val.isLt; omega) p := by
    exact odd_scalar_layer_growth_open hh hn (by have := b.property; omega)
      (by have := b.val.isLt; omega) (hcount b.val.val b.property (by have := b.val.isLt; omega))
  choose D hD hgood using hi
  have hnz (i : I) : D i≠0 := by
    obtain ⟨p,hp⟩ := hD i
    intro hz
    exact hp (by rw [hz,map_zero])
  obtain ⟨x,hx⟩ := Quartic.nonempty_principal_intersection D hnz
  refine ⟨∏ i,D i,⟨(Module.finBasis K _).equivFun.symm x,?_⟩,?_⟩
  · simp only [LinearEquiv.apply_symm_apply,map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  · intro p hp b hb hbd
    let i : I := ⟨⟨b,by omega⟩,hb⟩
    apply hgood i p
    rw [map_prod] at hp
    exact Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)

theorem eventually_odd_scalar_layers_open {h d : ℕ}
    (hd : 3≤d) (hh : 0<h) (qS qO : ℕ → ℕ)
    (hS : Tendsto (fun n : ℕ => (qS n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hO : Tendsto (fun n : ℕ => (qO n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,HasOddScalarLayersOpen K h n d (qO n) (qS n)
      ⌊oddRowExtraDensity d*(n : ℝ)^d⌋₊ := by
  let I := {b : Fin (d+1) // 3≤b.val}
  have hall : ∀ᶠ n : ℕ in atTop,∀ b : I,
      OddLayerCount h n d (qS n) (qO n) ⌊oddRowExtraDensity d*(n : ℝ)^d⌋₊ b.val.val := by
    apply Filter.eventually_all.mpr
    intro b
    exact eventually_augmented_higher_odd_row_budget hd b.property
      (by have := b.val.isLt; omega) hh qS qO hS hO
  filter_upwards [hall,eventually_gt_atTop 0] with n hn hn0
  apply odd_scalar_layers_open hh hn0
  intro b hb hbd
  exact hn ⟨⟨b,by omega⟩,hb⟩

end Froberg
