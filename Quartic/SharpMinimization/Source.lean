import Quartic.SharpMinimization.Slices

/-! The exact source sharp profile has a minimum on the six prefix edges. -/
namespace Quartic.SharpMinimization
open Quartic.UniformSurplus
noncomputable section

theorem sourceSharp_concave (m c i : ℕ) (hi : i ≤ ProfileCertificate.coreA c) :
    ConcaveOn ℝ (layerBox (ProfileCertificate.freeW m c))
      (fun n => sourceSharp m c i (n 0) (n 1) (n 2)) := by
  have hiR : (i:ℝ) ≤ (ProfileCertificate.coreA c:ℝ) := by exact_mod_cast hi
  have hA : (0:ℝ) ≤ (ProfileCertificate.coreA c:ℝ) := by positivity
  have he₁ : 0 ≤ max ((ProfileCertificate.coreA c:ℝ)/2-(i:ℝ)) 0 := le_max_right _ _
  have he₂ : 0 ≤ (ProfileCertificate.coreA c:ℝ)-max (i:ℝ) ((ProfileCertificate.coreA c:ℝ)/2) :=
    sub_nonneg.mpr (max_le hiR (by linarith))
  have h := layerPolynomial_concave (ProfileCertificate.freeW m c)
    ((SharpCertificate.coreShadow c i:ℝ)*(ProfileCertificate.freeW m c:ℝ)+
      (i:ℝ)*quadraticReal (ProfileCertificate.freeW m c))
    ((ProfileCertificate.coreB c:ℝ)-(SharpCertificate.coreShadow c i:ℝ))
    (max ((ProfileCertificate.coreA c:ℝ)/2-(i:ℝ)) 0)
    ((ProfileCertificate.coreA c:ℝ)-max (i:ℝ) ((ProfileCertificate.coreA c:ℝ)/2)) he₁ he₂
  convert h using 1
  funext n
  unfold sourceSharp sharpReal layerPolynomial
  ring

theorem edgePoint_ordered (w s : ℝ) (e : Fin 6) (_hw : 0 ≤ w) (he : EdgeFeasible w s e) :
    0 ≤ edgePoint w s e 2 ∧ edgePoint w s e 2 ≤ edgePoint w s e 1 ∧
      edgePoint w s e 1 ≤ edgePoint w s e 0 ∧ edgePoint w s e 0 ≤ w := by
  fin_cases e <;> norm_num [EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] at he
  all_goals norm_num [edgePoint]
  all_goals constructor <;> linarith [he.1,he.2]

/-- The numerical reduction asserted in `sc:sharp-profile`: every ordered real
profile admits a no-larger sharp value on an edge, preserving the source sum. -/
theorem source_edge_reduction (m c i : ℕ) (hi : i ≤ ProfileCertificate.coreA c)
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m c:ℝ)) :
    ∃e:Fin 6, EdgeFeasible (ProfileCertificate.freeW m c) (n₁+n₂+n₃) e ∧
      sourceSharp m c i (edgePoint (ProfileCertificate.freeW m c) (n₁+n₂+n₃) e 0)
        (edgePoint (ProfileCertificate.freeW m c) (n₁+n₂+n₃) e 1)
        (edgePoint (ProfileCertificate.freeW m c) (n₁+n₂+n₃) e 2) ≤
      sourceSharp m c i n₁ n₂ n₃ := by
  exact exists_prefix_edge_le _ _ _ _ _ (by positivity) hn rfl
    (fun n => sourceSharp m c i (n 0) (n 1) (n 2)) (sourceSharp_concave m c i hi)

/-- At fixed core dimension and fixed free-layer sum, the global sharp minimum
is attained at one of the six feasible prefix edges. -/
theorem source_minimum_on_edge (m c i : ℕ) (hi : i ≤ ProfileCertificate.coreA c)
    (s n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m c:ℝ))
    (hs : n₁+n₂+n₃=s) :
    ∃e:Fin 6, EdgeFeasible (ProfileCertificate.freeW m c) s e ∧
      ∀x₁ x₂ x₃:ℝ,
        (0 ≤ x₃ ∧ x₃ ≤ x₂ ∧ x₂ ≤ x₁ ∧ x₁ ≤ (ProfileCertificate.freeW m c:ℝ)) →
        x₁+x₂+x₃=s →
        sourceSharp m c i (edgePoint (ProfileCertificate.freeW m c) s e 0)
          (edgePoint (ProfileCertificate.freeW m c) s e 1)
          (edgePoint (ProfileCertificate.freeW m c) s e 2) ≤ sourceSharp m c i x₁ x₂ x₃ := by
  classical
  obtain ⟨e,he,_⟩ := source_edge_reduction m c i hi n₁ n₂ n₃ hn
  rw [hs] at he
  let Edges := {e:Fin 6 // EdgeFeasible (ProfileCertificate.freeW m c) s e}
  let : Nonempty Edges := ⟨⟨e,he⟩⟩
  obtain ⟨emin,hmin⟩ := Finite.exists_min (fun e:Edges =>
    sourceSharp m c i (edgePoint (ProfileCertificate.freeW m c) s e 0)
      (edgePoint (ProfileCertificate.freeW m c) s e 1) (edgePoint (ProfileCertificate.freeW m c) s e 2))
  refine ⟨emin,emin.property,?_⟩
  intro x₁ x₂ x₃ hx hsum
  obtain ⟨e',he',hle⟩ := source_edge_reduction m c i hi x₁ x₂ x₃ hx
  rw [hsum] at he' hle
  exact (hmin ⟨e',he'⟩).trans hle

end
end Quartic.SharpMinimization
