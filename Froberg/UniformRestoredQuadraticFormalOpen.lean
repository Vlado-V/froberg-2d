module

public import Froberg.UniformActualRestoredQuadratic
public import Froberg.RestoredQuadraticFormalSeparation
public import Froberg.QuadraticDetectorSupport
public import Froberg.RestoredQuadraticOpenProperty

@[expose] public section

/-! Actual enlarged restored families satisfy C.2 on a nonempty open.
The scalar threshold precedes every choice of the shared quadratic frame. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module Filter MvPolynomial

theorem uniform_exact_counts_restored_formal_quadratic_open {d k h lo : ℕ}
    (hd : 3≤d) (he : d%2=0) (hh : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (extra : ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], ∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j)
      (slot : Fin (actualRestoredPureCount K d h) →
        Fin (actualRestoredSize K d h n (e n) extra))
      (c : ℕ) (T : Poly K h →ₗ[K] (Fin c → K)),
      T.comp (homogeneousComponent 2)=T → O 2≤T.ker →
      ∀ o : Fin (outerColumnCount d h) → Forms K h 1,
      LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)) →
      HasRestoredFormalQuadraticOpen (m := n) (f := f n) (by omega) he hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2)
        (actualRestoredIndex K d h n (e n) extra) slot := by
  filter_upwards [uniform_exact_counts_restored_quadratic_open hd hh upper a f e extra hc]
    with n hn
  intro K _ _ O hO slot c T hT hO₂ o ho
  obtain ⟨D,hD,hgood⟩  := hn K O hO c T o ho
  letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
    (actualRestoredCounts K d h n (e n) extra) O) := finite_space hO
  refine ⟨D,hD,?_⟩
  intro p hp
  exact QuadraticSeparated.restored_formal hd (by omega) he hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (fun j hj => (mem_allEvenIndices.mp hj).1)
    (actualRestoredIndex K d h n (e n) extra) slot T hT hO₂ p (hgood p hp)

/-- The quadratic quotient supplied by the common frame open satisfies
all detector assumptions, so no further choice of output space is needed. -/
theorem uniform_exact_counts_restored_frame_quadratic_open {d k h lo : ℕ}
    (hd : 3≤d) (he : d%2=0) (hh : 0<h)
    (upper : Bool) (a f e : ℕ → ℕ) (extra : ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], ∀ frame : Fin (quadraticOutputDimension d h) → Forms K h 2,
      ∀ slot : Fin (actualRestoredPureCount K d h) →
        Fin (actualRestoredSize K d h n (e n) extra),
      ∀ (c : ℕ) (T : Forms K h 2 →ₗ[K] (Fin c → K)),
      T.ker=Submodule.span K (Set.range frame) →
      ∀ o : Fin (outerColumnCount d h) → Forms K h 1,
      LinearIndependent K (fun p => quadraticPolynomialDetector T
        (pairProducts (fun i => (o i).val) p)) →
      HasRestoredFormalQuadraticOpen (m := n) (f := f n) (by omega) he
        (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
        (fun j hj => (mem_allEvenIndices.mp hj).2.1)
        (fun j hj => (mem_allEvenIndices.mp hj).2.2)
        (actualRestoredIndex K d h n (e n) extra) slot := by
  filter_upwards [uniform_exact_counts_restored_formal_quadratic_open hd he hh upper a f e extra hc]
    with n hn
  intro K _ _ frame slot c T hT o ho
  apply hn K (targetLayerOutput frame)
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j) slot c
    (quadraticPolynomialDetector T) (quadraticPolynomialDetector_supported T) _ o ho
  simpa [targetLayerOutput] using quadraticPolynomialDetector_frame frame T hT

end Froberg.PreparedParameters
