module

public import Froberg.CountedPreparedOuterOpen
public import Froberg.UniformQuadraticScalarData
public import Froberg.UniformSharedQuadraticFrame

@[expose] public section

/-! Field-uniform thresholds for the actual counted prepared C.2 open. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module Filter MvPolynomial PreparedParameters PreparedTarget FullPreparedParameters PrivateColumns
open scoped Topology

theorem eventually_uniform_prepared_outer_open_from_shared_detector {d h : ℕ}
    (hd : 3≤d) (ho : d%2=1) (hh : 0 < h) (r f : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1))
      atTop (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) (u : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
      ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
        (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
        (hmin : ∀ j∈J,2≤j) (idx : Fin (r n) ≃ PreparedParameters.Label (upperCount n d) J counts)
        (c : ℕ) (e : (Fin h → K) ≃ₗ[K] Forms K h 1)
        (L : Forms K h 2 →ₗ[K] (Fin c → K)) (w : Fin u → Fin h → K)
        (o : Fin (outerColumnCount d h) → Forms K h 1),
        O 2≤(quadraticPolynomialDetector L).ker →
        LinearIndependent K (fun p => quadraticPolynomialDetector L
          (pairProducts (fun i => (o i).val) p)) →
        (privatePolynomialMap (a := n-u) (s := d-1) (Function.Embedding.refl (Fin u))
          (fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
          Submodule.span K (Set.range (koszulVector
            (privateGenerator (a := n-u) (s := d-1) (Function.Embedding.refl (Fin u)) w))) →
        HasUniformPreparedOuterOpen (n := n) (q := upperCount n d) (f := f n) (u := u)
          (counts := counts) (by omega) ho hO hJ heven := by
  filter_upwards [eventually_uniform_quadratic_scalar_data hd hh r f hr hf u] with n hn
  intro K _ _ J counts O hO hJ heven hmin idx c e L w o hO₂ hdet hker
  obtain ⟨a,ha,Q,hQ,C,hCdeg,hC,hCQ,hcap⟩ := hn K
  subst n
  have hker' : (privatePolynomialMap (a := a) (s := d-1) (Function.Embedding.refl (Fin u))
      (fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
      Submodule.span K (Set.range (koszulVector
        (privateGenerator (a := a) (s := d-1) (Function.Embedding.refl (Fin u)) w))) := by
    let KP : ℕ → Prop := fun v =>
      (privatePolynomialMap (a := v) (s := d-1) (Function.Embedding.refl (Fin u))
        (fun i => (L.comp (mulForm (e (w i)))).comp e.toLinearMap)).ker=
        Submodule.span K (Set.range (koszulVector
          (privateGenerator (a := v) (s := d-1) (Function.Embedding.refl (Fin u)) w)))
    exact Eq.mp (congrArg KP (Nat.add_sub_cancel a u)) hker
  exact prepared_outer_open_of_detected_scalar_witness hd ho hO hJ heven hmin idx e L hO₂ w
    (Function.Embedding.refl (Fin u)) hker' Q hQ o hdet C hCdeg hC hCQ
    (by simpa only [Fintype.card_fin] using hcap)

theorem eventually_uniform_counted_prepared_outer_open {d : ℕ} (hd : 3≤d) (ho : d%2=1) :
    ∀ᶠ h : ℕ in atTop, ∀ (r f : ℕ → ℕ),
      Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
        atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
      Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1))
        atTop (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ u : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
        ∃ P : MvPolynomial (Fin (finrank K
          (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x P≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) P≠0 →
            ∀ (J : Finset ℕ) (counts : ℕ → ℕ) (O : ℕ → Submodule K (Poly K h))
              (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
              (hmin : ∀ j∈J,2≤j)
              (idx : Fin (r n) ≃ PreparedParameters.Label (upperCount n d) J counts),
              O 2≤outputFrameSpace frame →
              HasUniformPreparedOuterOpen (n := n) (q := upperCount n d) (f := f n) (u := u)
                (counts := counts) (by omega) ho hO hJ heven := by
  filter_upwards [eventually_uniform_counted_shared_quadratic_frame hd,
    eventually_gt_atTop (0 : ℕ)] with h hshared hh
  intro r f hr hf u
  filter_upwards [eventually_uniform_prepared_outer_open_from_shared_detector hd ho hh r f hr hf u]
    with n hn
  intro K _ _
  obtain ⟨o,_,hopen⟩ := hshared K
  obtain ⟨e,w,P,_,hP,hgood⟩ := hopen (n-u) u u (Function.Embedding.refl (Fin u))
  refine ⟨P,hP,?_⟩
  intro frame hframe J counts O hO hJ heven hmin idx hO₂
  obtain ⟨L,hL,hdet,hker⟩ := hgood frame hframe
  exact hn K J counts O hO hJ heven hmin idx _ e L w o
    (hO₂.trans (quadraticPolynomialDetector_frame frame L hL)) hdet hker

theorem eventually_uniform_allEven_prepared_outer_open {d : ℕ} (hd : 3≤d) (ho : d%2=1) :
    ∀ᶠ h : ℕ in atTop, ∀ (e f : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) →
      Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1))
        atTop (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) →
      ∀ u : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K],
        ∃ P : MvPolynomial (Fin (finrank K
          (Fin (quadraticOutputDimension d h) → Forms K h 2))) K,
          (∃ x,eval x P≠0) ∧
          ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
            eval ((Module.finBasis K _).equivFun frame) P≠0 →
            ∀ (O : ℕ → Submodule K (Poly K h))
              (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j),
              O 2≤outputFrameSpace frame →
              HasUniformPreparedOuterOpen (n := n) (q := upperCount n d) (f := f n) (u := u)
                (counts := allEvenCount d h n (e n+1)) (by omega) ho hO
                (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
                (fun _ hj => (mem_allEvenIndices.mp hj).2.2) := by
  filter_upwards [eventually_uniform_counted_prepared_outer_open hd ho] with h hh
  intro e f he hf u
  let r := fun n => Fintype.card (PreparedParameters.Label (upperCount n d)
    (allEvenIndices d) (allEvenCount d h n (e n+1)))
  have hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    allEvenLabel_count_limit hd h 1 e he
  filter_upwards [hh r f hr hf u] with n hn
  intro K _ _
  obtain ⟨P,hP,hgood⟩ := hn K
  refine ⟨P,hP,?_⟩
  intro frame hframe O hO hO₂
  exact hgood frame hframe (allEvenIndices d) (allEvenCount d h n (e n+1)) O hO
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun _ hj => (mem_allEvenIndices.mp hj).1) (Fintype.equivFin _).symm hO₂


end Froberg
