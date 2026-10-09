module

public import Froberg.FullPreparedFibers
public import Froberg.ParameterPullbackOpen

@[expose] public section

/-! Surjective parameter projections let the prepared rows, the scalar
background, and the outer/private linear parts impose conditions on one
and the same fixed-pure parameter space. -/
noncomputable section
namespace Froberg.FullPreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

def preparedProjection : FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
    PreparedParameters.Space m d q J counts O where
  toFun p := p.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem preparedProjection_surjective : Function.Surjective
    (preparedProjection (K := K) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) := by
  intro p
  exact ⟨(0,(p,0)),rfl⟩

abbrev BackgroundSpace (m d q f : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) :=
  PreparedTarget.OuterSpace K σ m d f × (PreparedParameters.Label q J counts → Forms K m d)

def backgroundProjection : FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
    BackgroundSpace (K := K) (σ := σ) m d q f J counts where
  toFun p := (p.2.2,p.2.1.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem backgroundProjection_surjective : Function.Surjective
    (backgroundProjection (K := K) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) := by
  intro p
  exact ⟨(0,((p.2,0),p.1)),rfl⟩

def outerPrivateProjection : FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
    (PreparedTarget.OuterSpace K σ m d f × PreparedTarget.OuterSpace K σ m d u) where
  toFun p := (p.2.2,p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem outerPrivateProjection_surjective : Function.Surjective
    (outerPrivateProjection (K := K) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) := by
  intro p
  exact ⟨(p.2,((0,0),p.1)),rfl⟩

end Froberg.FullPreparedParameters
