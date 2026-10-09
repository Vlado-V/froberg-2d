module

public import Quartic.SharpMinimization.Source
public import Quartic.SharpCertificate

@[expose] public section

/-! Extension of the finite sharp edge certificates to all ordered real
profiles having an integral total source dimension. -/
namespace Quartic.SharpMinimization
open Quartic.UniformSurplus Quartic.UniformScalar
open Quartic.HullCertificate Quartic.FiniteCounts
noncomputable section

/-- The existing scalar incidence tests, allowing a real image lower bound. -/
def ImageBoundsReal (s : Scalars) (E : ℝ) (d : ℤ) : Prop :=
  (d:ℝ)*((s.q:ℝ)+(s.a:ℝ)-(d:ℝ)) ≤ E ∧
    (covectorR s.j E s.q s.a d < 0 ∨
      covectorR s.j E s.q s.a d-(codimension s d:ℝ) ≤ (target s:ℝ))

theorem imageBounds_cast {s : Scalars} {E : ℚ} {d : ℤ} (h : ImageBounds s E d) :
    ImageBoundsReal s (E:ℝ) d := by
  refine ⟨?_,?_⟩
  · exact_mod_cast h.1
  · rcases h.2 with hneg | hnorm
    · left
      unfold covectorR
      unfold covectorBound at hneg
      exact_mod_cast hneg
    · right
      unfold covectorR
      unfold covectorBound at hnorm
      exact_mod_cast hnorm

theorem ImageBoundsReal.mono {s : Scalars} {E E' : ℝ} {d : ℤ}
    (h : ImageBoundsReal s E d) (hE : E ≤ E') : ImageBoundsReal s E' d := by
  refine ⟨h.1.trans hE,?_⟩
  have hcov : covectorR s.j E' s.q s.a d ≤ covectorR s.j E s.q s.a d := by
    unfold covectorR
    linarith
  rcases h.2 with hneg | hnorm
  · exact Or.inl (hcov.trans_lt hneg)
  · right
    linarith

theorem edgePoint_eq_rational (p : SharpCertificate.Parameters) (e : Fin 6) (d : ℤ) (k : Fin 3) :
    edgePoint (p.w:ℝ) ((d:ℝ)-(p.i:ℝ)) e k =
      (SharpCertificate.edgeLayer p.w (SharpCertificate.edgeIntermediate p e d)
        (SharpCertificate.edgeLeft e) (SharpCertificate.edgeRight e) (k.val+1):ℝ) := by
  fin_cases e <;> fin_cases k <;>
    norm_num [edgePoint,SharpCertificate.edgeLayer,SharpCertificate.edgeIntermediate,
      SharpCertificate.edgeLeft,SharpCertificate.edgeRight,SharpCertificate.edgeWidth]

/-- At integral source dimension, the real edge values are exactly the casts
of the rational expressions already checked by the finite certificates. -/
theorem sourceSharp_edge_cast (m c i : ℕ) (e : Fin 6) (d : ℤ) :
    sourceSharp m c i (edgePoint (ProfileCertificate.freeW m c) ((d:ℝ)-(i:ℝ)) e 0)
      (edgePoint (ProfileCertificate.freeW m c) ((d:ℝ)-(i:ℝ)) e 1)
      (edgePoint (ProfileCertificate.freeW m c) ((d:ℝ)-(i:ℝ)) e 2) =
      (SharpCertificate.sharpEdge (SharpCertificate.parameters m c i) e d:ℝ) := by
  have h₀ := edgePoint_eq_rational (SharpCertificate.parameters m c i) e d 0
  have h₁ := edgePoint_eq_rational (SharpCertificate.parameters m c i) e d 1
  have h₂ := edgePoint_eq_rational (SharpCertificate.parameters m c i) e d 2
  norm_num only [SharpCertificate.parameters,Int.cast_natCast,Fin.val_zero,Fin.val_one,
    Fin.val_ofNat,Nat.reduceAdd,Nat.reduceMod] at h₀ h₁ h₂
  rw [h₀,h₁,h₂,sourceSharp_eq_rational]
  rfl

/-- The finite sharp certificate now applies to every ordered real profile,
rather than merely to the six edges. -/
theorem finite_sharp_profile_bounds (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ))
    (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d < (ProfileCertificate.totalA m (mixedCount m upper):ℤ))
    (hd : (i:ℝ)+n₁+n₂+n₃=(d:ℝ)) :
    ImageBoundsReal (scalars m (upperEndpoint m) (mixedCount m upper))
      (sourceSharp m (mixedCount m upper) i n₁ n₂ n₃) d := by
  have hsum : n₁+n₂+n₃=(d:ℝ)-(i:ℝ) := by linarith
  obtain ⟨e,he,hle⟩ := source_edge_reduction m (mixedCount m upper) i hi n₁ n₂ n₃ hn
  rw [hsum] at he hle
  rw [sourceSharp_edge_cast] at hle
  have hlo : (i:ℤ)+(SharpCertificate.edgeLeft e:ℤ)*(ProfileCertificate.freeW m (mixedCount m upper):ℤ) ≤ d := by
    have hr : (i:ℝ)+(SharpCertificate.edgeLeft e:ℝ)*(ProfileCertificate.freeW m (mixedCount m upper):ℝ) ≤ (d:ℝ) := by
      linarith [he.1]
    exact_mod_cast hr
  have hhi : d ≤ (i:ℤ)+(SharpCertificate.edgeRight e:ℤ)*(ProfileCertificate.freeW m (mixedCount m upper):ℤ) := by
    have hr : (d:ℝ) ≤ (i:ℝ)+(SharpCertificate.edgeRight e:ℝ)*(ProfileCertificate.freeW m (mixedCount m upper):ℝ) := by
      linarith [he.2]
    exact_mod_cast hr
  have h := SharpCertificate.sharp_edge_inequalities m hmlo hmhi upper i hi e d ⟨hdlo,hdhi,hlo,hhi⟩
  exact (imageBounds_cast h).mono hle

/-- The outer inequality on the entire source range, including d=a. -/
theorem finite_sharp_outer (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ))
    (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d ≤ (ProfileCertificate.totalA m (mixedCount m upper):ℤ))
    (hd : (i:ℝ)+n₁+n₂+n₃=(d:ℝ)) :
    (d:ℝ)*((upperEndpoint m:ℝ)+(ProfileCertificate.totalA m (mixedCount m upper):ℝ)-(d:ℝ)) ≤
      sourceSharp m (mixedCount m upper) i n₁ n₂ n₃ := by
  by_cases hlt : d < (ProfileCertificate.totalA m (mixedCount m upper):ℤ)
  · exact (finite_sharp_profile_bounds m hmlo hmhi upper i hi n₁ n₂ n₃ hn d hdlo hlt hd).1
  have hdeq : d=(ProfileCertificate.totalA m (mixedCount m upper):ℤ) := by omega
  have hdR : (d:ℝ)=(ProfileCertificate.coreA (mixedCount m upper):ℝ)+
      3*(ProfileCertificate.freeW m (mixedCount m upper):ℝ) := by
    rw [hdeq,Int.cast_natCast,source_total]
  have hiR : (i:ℝ) ≤ (ProfileCertificate.coreA (mixedCount m upper):ℝ) := by exact_mod_cast hi
  have hn₂ : n₂ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ) := hn.2.2.1.trans hn.2.2.2
  have hn₃ : n₃ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ) := hn.2.1.trans hn₂
  have hieqR : (i:ℝ)=(ProfileCertificate.coreA (mixedCount m upper):ℝ) := by linarith [hn.2.2.2]
  have hieq : i=ProfileCertificate.coreA (mixedCount m upper) := by exact_mod_cast hieqR
  have hn₁eq : n₁=(ProfileCertificate.freeW m (mixedCount m upper):ℝ) := by linarith
  have hn₂eq : n₂=(ProfileCertificate.freeW m (mixedCount m upper):ℝ) := by linarith [hn.2.2.2]
  have hn₃eq : n₃=(ProfileCertificate.freeW m (mixedCount m upper):ℝ) := by linarith [hn.2.2.2]
  rw [hieq,hn₁eq,hn₂eq,hn₃eq,hdeq,Int.cast_natCast]
  have h := SharpCertificate.full_profile_outer m hmlo hmhi upper
  have hreal : (upperEndpoint m:ℝ)*(ProfileCertificate.totalA m (mixedCount m upper):ℝ) ≤
      sourceSharp m (mixedCount m upper) (ProfileCertificate.coreA (mixedCount m upper))
        (ProfileCertificate.freeW m (mixedCount m upper))
        (ProfileCertificate.freeW m (mixedCount m upper))
        (ProfileCertificate.freeW m (mixedCount m upper)) := by
    rw [←Rat.cast_natCast (α:=ℝ) (ProfileCertificate.freeW m (mixedCount m upper)),
      sourceSharp_eq_rational]
    exact_mod_cast h
  nlinarith only [hreal]

end
end Quartic.SharpMinimization
