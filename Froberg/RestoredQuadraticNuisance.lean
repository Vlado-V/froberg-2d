import Froberg.RestoredQuadraticSeparationOpen

/-! The genuine coefficient-row open implies C.2 for every scalar-supported
endpoint deletion and the literal restored background. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f c : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

/-- Empty private columns contribute no nuisance row. -/
theorem quadraticSeparated_empty_private
    (T : Poly K h →ₗ[K] (Fin c → K))
    (p : QuadraticParameters K h m d r f) (hp : QuadraticSeparated T p) :
    ∀ x a, quadraticNuisanceRow (t := d-2)
      (FullBiform K (Fin h) m 1 (d-1)).subtype (biformVectorDetector T)
      p.1 (Fin.elim0 : Fin 0 → FullBiform K (Fin h) m 1 (d-1)) x+
      detectedSymmetricProductRow (FullBiform K (Fin h) m 1 (d-1)).subtype
        (biformVectorDetector T) p.2 a=0 → a=0 := by
  intro x a ha
  apply hp x.1 a
  simpa only [quadraticNuisanceRow,addRow_apply,PolynomialRestoration.row,
    LinearMap.coe_mk,AddHom.coe_mk,Finset.univ_eq_empty,Finset.sum_empty,
    map_zero,add_zero] using ha

end Froberg.PreparedParameters
