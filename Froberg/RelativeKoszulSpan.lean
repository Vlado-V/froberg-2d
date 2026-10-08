import Froberg.RelativeKoszulExactness
import Froberg.Koszul

/-! Boundary support for the relative quotient sequence, including the
constant cross-parity Koszul generators. -/
noncomputable section
namespace Froberg.RelativeKoszul
open Module
variable {K U V W ι : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [Fintype ι] [DecidableEq ι]

/-- It suffices to check new-coordinate support on the displayed boundary
vectors; taking their linear span introduces no extra requirement. -/
theorem new_coordinates_mem_of_span (R : Submodule K V) (S : Set (U × (ι → V)))
    (hS : ∀ x ∈ S, ∀ i, x.2 i ∈ R) {x : U × (ι → V)}
    (hx : x ∈ Submodule.span K S) : ∀ i, x.2 i ∈ R := by
  have hle : Submodule.span K S ≤
      (sourceRelations (ι := ι) R).comap (LinearMap.snd K U (ι → V)) := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.mem_pi.mpr (fun i _ => hS x hx i)
  exact fun i => Submodule.mem_pi.mp (hle hx) i (Set.mem_univ i)

theorem multiplication_injective_of_span (old : U →ₗ[K] W)
    (fresh : (ι → V) →ₗ[K] W) (R : Submodule K V) (S : Set (U × (ι → V)))
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range)
    (hcycles : (old.coprod fresh).ker ≤ Submodule.span K S)
    (hS : ∀ x ∈ S, ∀ i, x.2 i ∈ R) :
    Function.Injective (multiplication old fresh R hrel) :=
  multiplication_injective old fresh R (Submodule.span K S).subtype hrel
    (by simpa only [Submodule.range_subtype] using hcycles)
    (fun c => new_coordinates_mem_of_span R S hS c.property)

theorem target_finrank_of_span [FiniteDimensional K V] [FiniteDimensional K W]
    (old : U →ₗ[K] W) (fresh : (ι → V) →ₗ[K] W)
    (R : Submodule K V) (S : Set (U × (ι → V)))
    (hrel : ∀ v : ι → V, (∀ i, v i ∈ R) → fresh v ∈ old.range)
    (hcycles : (old.coprod fresh).ker ≤ Submodule.span K S)
    (hS : ∀ x ∈ S, ∀ i, x.2 i ∈ R) :
    finrank K (W ⧸ old.range) =
      finrank K (W ⧸ (old.range ⊔ fresh.range)) + Fintype.card ι * finrank K (V ⧸ R) :=
  target_finrank old fresh R (Submodule.span K S).subtype hrel
    (by simpa only [Submodule.range_subtype] using hcycles)
    (fun c => new_coordinates_mem_of_span R S hS c.property)

/-- A cross-parity constant Koszul vector, read at a new even generator,
contains only an old odd generator. This purely linear fact applies to any
parity labels and any distinguished even label. -/
theorem cross_koszul_coordinate_mem {r : ℕ} {P : Type*}
    (q : Fin r → V) (parity : Fin r → P) (even : P) (R : Submodule K V)
    (hodd : ∀ j, parity j ≠ even → q j ∈ R)
    (i : Fin r) (hi : parity i=even) (p : GeneratorPair r)
    (hp : parity p.val.1 ≠ parity p.val.2) : koszulVector q p i ∈ R := by
  classical
  unfold koszulVector
  apply R.sub_mem
  · split_ifs with he
    · apply hodd
      intro hbad
      apply hp
      rw [←he,hi,hbad]
    · exact R.zero_mem
  · split_ifs with he
    · apply hodd
      intro hbad
      apply hp
      rw [←he,hi,hbad]
    · exact R.zero_mem

/-- The same support statement for every linear combination of actual
cross-parity Koszul vectors. -/
theorem cross_koszul_span_coordinate_mem {r : ℕ} {P : Type*}
    (q : Fin r → V) (parity : Fin r → P) (even : P) (R : Submodule K V)
    (hodd : ∀ j, parity j ≠ even → q j ∈ R)
    (i : Fin r) (hi : parity i=even) {x : Fin r → V}
    (hx : x ∈ Submodule.span K
      (koszulVector q '' {p : GeneratorPair r | parity p.val.1 ≠ parity p.val.2})) :
    x i ∈ R := by
  have hle : Submodule.span K
      (koszulVector q '' {p : GeneratorPair r | parity p.val.1 ≠ parity p.val.2}) ≤
      R.comap (LinearMap.proj i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact cross_koszul_coordinate_mem q parity even R hodd i hi p hp
  exact hle hx

end Froberg.RelativeKoszul
