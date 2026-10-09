module

public import Froberg.BiformNormalized
public import Froberg.BilinearPostcompose
public import Froberg.TwoFamilyIntrinsicOpen

@[expose] public section

/-! Actual two-block homogeneous multiplication with explicit target-degree
identifications. These maps feed the two-family odd-row incidence theorem. -/
noncomputable section
namespace Froberg
open Module TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type*} [Field K]
variable {h n a b c e r t : ℕ}

def formDegreeEquiv {n a b : ℕ} (hab : a=b) : Forms K n a ≃ₗ[K] Forms K n b :=
  LinearEquiv.ofEq _ _ (congrArg (Forms K n) hab)

def tensorDegreeEquiv (hx : a+b=r) (hy : e+c=t) :
    Forms K h (a+b) ⊗[K] Forms K n (e+c) ≃ₗ[K]
      Forms K h r ⊗[K] Forms K n t :=
  TensorProduct.congr (formDegreeEquiv hx) (formDegreeEquiv hy)

/-- Multiply genuine homogeneous tensors, with only target degree equalities
used to put different sources in one common target. -/
def biformAction (hx : a+b=r) (hy : e+c=t) :
    (Forms K h a ⊗[K] Forms K n c) →ₗ[K]
      (Forms K h b ⊗[K] Forms K n e) →ₗ[K]
        (Forms K h r ⊗[K] Forms K n t) :=
  (tensorFormProduct (d := c) (gradedMultiplication (K := K) (n := h) (d := a) (e := b))).compr₂ₛₗ
    (tensorDegreeEquiv hx hy).toLinearMap

/-- Exact normalized growth survives these harmless degree identifications. -/
theorem biformAction_growth (hh : 0<h) (hn : 0<n)
    (hx : a+b=r) (hy : e+c=t)
    (L : Submodule K (Forms K h b ⊗[K] Forms K n e)) :
    (h+r-1).choose r*(n+t-1).choose t*finrank K L ≤
      (h+b-1).choose b*(n+e-1).choose e*
        finrank K (BilinearImage.image (K := K) (F := Forms K h a ⊗[K] Forms K n c) (V := Forms K h b ⊗[K] Forms K n e) (W := Forms K h r ⊗[K] Forms K n t) (biformAction (K := K) (h := h) (n := n) (a := a) (b := b) (c := c) (e := e) (r := r) (t := t) hx hy) L) := by
  rw [biformAction]
  rw [bilinearImage_postcompose
    (P := Forms K h a ⊗[K] Forms K n c)
    (V := Forms K h b ⊗[K] Forms K n e)
    (W := Forms K h (a+b) ⊗[K] Forms K n (e+c))
    (Z := Forms K h r ⊗[K] Forms K n t)]
  rw [(tensorDegreeEquiv (K := K) (h := h) (n := n) hx hy).finrank_map_eq]
  subst r
  subst t
  simpa only [Nat.add_comm a b,Nat.add_assoc] using biform_normalized_growth (a := a) (c := c) hh hn L

/-- Scalar and linear-output parameter actions have the same degree-b target. -/
def oddRowScalarAction {d b : ℕ} (hb : b≤d) :
    (Forms K h 0 ⊗[K] Forms K n d) →ₗ[K]
      (Forms K h b ⊗[K] Forms K n (d-b)) →ₗ[K]
        (Forms K h b ⊗[K] Forms K n (2*d-b)) :=
  biformAction (by omega) (by omega)

def oddRowLinearAction {d b : ℕ} (hb : 1≤b) (hbd : b≤d) :
    (Forms K h 1 ⊗[K] Forms K n (d-1)) →ₗ[K]
      (Forms K h (b-1) ⊗[K] Forms K n (d-b+1)) →ₗ[K]
        (Forms K h b ⊗[K] Forms K n (2*d-b)) :=
  biformAction (by omega) (by omega)

end Froberg
