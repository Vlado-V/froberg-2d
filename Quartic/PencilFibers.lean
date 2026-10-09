module

public import Quartic.SymmetricEvaluation

@[expose] public section

/-!
# Fibers of a two-dimensional tensor factor

In coordinates `Z ⊗ K² = Z × Z`, two distinct binary directions give disjoint
copies of their fiber spaces inside the same subspace. This is the elementary
dimension estimate used before symmetric evaluation in the convolution proof.
-/

noncomputable section

namespace Quartic.PencilFibers

open Module

variable {K Z : Type*} [Field K] [AddCommGroup Z] [Module K Z]
  [FiniteDimensional K Z]

def graph (t : K) : Z →ₗ[K] (Z × Z) :=
  LinearMap.id.prod (t • LinearMap.id)

def fiber (P : Submodule K (Z × Z)) (t : K) : Submodule K Z := P.comap (graph t)

theorem two_fibers_bound (P : Submodule K (Z × Z)) (s t : K) (hst : s ≠ t) :
    finrank K (fiber P s) + finrank K (fiber P t) ≤ finrank K P := by
  let J : (fiber P s × fiber P t) →ₗ[K] P :=
    LinearMap.codRestrict P
      (((graph s).comp (fiber P s).subtype).coprod
        ((graph t).comp (fiber P t).subtype))
      (fun a => P.add_mem a.1.property a.2.property)
  have hinj : Function.Injective J := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    have hfst : a.1.val + a.2.val = 0 := congrArg (fun z : P => z.val.1) ha
    have hsnd : s • a.1.val + t • a.2.val = 0 := congrArg (fun z : P => z.val.2) ha
    have hsecond : a.2.val = -a.1.val := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [add_comm] using hfst
    have hscalar : (s - t) • a.1.val = 0 := by
      rw [sub_smul]
      rw [hsecond, smul_neg] at hsnd
      simpa only [sub_eq_add_neg] using hsnd
    have hfirst : a.1.val = 0 := (smul_eq_zero.mp hscalar).resolve_left (sub_ne_zero.mpr hst)
    apply Prod.ext
    · exact Subtype.ext hfirst
    · apply Subtype.ext
      simpa [hfirst] using hsecond
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_prod] using h

theorem equal_fiber_bound (P : Submodule K (Z × Z)) (s t : K) (hst : s ≠ t)
    (b : ℕ) (hs : b ≤ finrank K (fiber P s)) (ht : b ≤ finrank K (fiber P t)) :
    b ≤ finrank K P / 2 := by
  have h := two_fibers_bound P s t hst
  omega

end Quartic.PencilFibers
