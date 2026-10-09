module

public import Froberg.MixedRestriction
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! The two generic vector conditions persist under extension of scalars. -/
noncomputable section
namespace Froberg.MixedExterior
open Matrix

lemma linearIndependent_map_coordinates {K L I J : Type*} [Field K] [Field L]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : K →+* L) (v : I → J → K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i j => f (v i j)) := by
  let A : Matrix J I K := fun j i => v i j
  have hA : Function.Injective A.mulVec := Matrix.mulVec_injective_iff.mpr hv
  obtain ⟨g,hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hA)
  let B := LinearMap.toMatrix' g
  have hBA : B*A=1 := by
    rw [← LinearMap.toMatrix'_toLin' A,← LinearMap.toMatrix'_comp,hg]
    exact LinearMap.toMatrix'_id
  have hmap : (B.map f)*(A.map f)=1 := by
    rw [← Matrix.map_mul,hBA]
    exact Matrix.map_one f f.map_zero f.map_one
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  change (A.map f).mulVec x=(A.map f).mulVec y at hxy
  have he := congrArg (fun z => (B.map f).mulVec z) hxy
  simpa only [Matrix.mulVec_mulVec,hmap,Matrix.one_mulVec] using he

lemma full_spark_map_coordinates {K L α : Type*} [Field K] [Field L]
    [Fintype α] [DecidableEq α] {h : ℕ} (f : K →+* L) (v : α → Fin h → K)
    (hv : ∀ S : Finset α,S.card ≤ h → LinearIndependent K (fun i : S => v i.val)) :
    ∀ S : Finset α,S.card ≤ h → LinearIndependent L (fun i : S => fun j => f (v i.val j)) := by
  intro S hS
  exact linearIndependent_map_coordinates f _ (hv S hS)

lemma UniversalMixedPosition.map_coordinates {K L α : Type*} [Field K] [Field L]
    [Fintype α] [DecidableEq α] {h : ℕ} (f : K →+* L) {v : α → Fin h → K}
    (hv : UniversalMixedPosition v) : UniversalMixedPosition (fun i j => f (v i j)) := by
  intro c
  have hm : (fun I J => mixedRow
      (paddedVectors (fun I => (c.2.1 I).val) c.2.2
        (fun a j => f (v a (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ c.1.isLt)) j))) I) J) =
      (fun I J => f (mixedRow
      (paddedVectors (fun I => (c.2.1 I).val) c.2.2
        (fun a j => v a (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ c.1.isLt)) j)) I) J)) := by
    funext I J
    rw [paddedVectors_map,mixedRow_map]
  rw [hm]
  let M := Matrix.of (fun I J => mixedRow
    (paddedVectors (fun I => (c.2.1 I).val) c.2.2
      (fun a j => v a (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ c.1.isLt)) j)) I) J)
  change Matrix.det (f.mapMatrix M) ≠ 0
  rw [← f.map_det]
  intro he
  apply hv c
  have hz : M.det=0 := f.injective (by simpa using he)
  exact hz

end Froberg.MixedExterior
