module

public import Froberg.PrivateFrameDetector

@[expose] public section

/-! The frame quotient detector only reads the quadratic component. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h c : ℕ}

theorem quadraticPolynomialDetector_supported
    (T : Forms K h 2 →ₗ[K] (Fin c → K)) :
    (quadraticPolynomialDetector T).comp (homogeneousComponent 2)=
      quadraticPolynomialDetector T := by
  apply LinearMap.ext
  intro p
  change T ⟨homogeneousComponent 2 (homogeneousComponent 2 p),_⟩=
    T ⟨homogeneousComponent 2 p,_⟩
  congr 1
  apply Subtype.ext
  exact homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous 2 p)

end Froberg
