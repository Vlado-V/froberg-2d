import Quartic.AlgebraicKernelAvoidance

/-! Eliminate the first constrained vector and obtain an equation only in
second-stage parameters. Every first-stage kernel vector is quantified. -/
noncomputable section
universe u
namespace Quartic.AlgebraicKernelAvoidance
open MvPolynomial Matrix Algebra
open RationalImageAvoidance KernelPolynomialCharts
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]

section TwoStage
variable [IsDomain R] {I : Type} {a b n l r s g : ℕ}

/-- Two dependent linear constraints over an arbitrary algebraic domain.
The second matrix is evaluated after the first motion is reconstructed.
Only the transcendence degree of the base enters the count: rationality of
the base is neither assumed nor concluded. -/
theorem equation_second_stage
    (base : I → R) (htr : trdeg K R ≤ g)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g+n < r+s) :
    ∃ P : MvPolynomial (Fin l) K, P ≠ 0 ∧
      ∀ (φ : R →ₐ[K] K) (x : Fin n → K) (y : Fin l → K),
        r ≤ (evaluated A (fun i => φ (base i))).rank →
        s ≤ (evaluated B (Sum.elim (fun i => φ (base i)) x)).rank →
        evaluated A (fun i => φ (base i)) *ᵥ x = 0 →
        evaluated B (Sum.elim (fun i => φ (base i)) x) *ᵥ y = 0 →
        eval y P = 0 := by
  classical
  let C₁ := (Fin r ↪ Fin a) × (Fin r ↪ Fin n)
  let C₂ := (Fin s ↪ Fin b) × (Fin s ↪ Fin l)
  let F₀ : I → MvPolynomial I K := fun i => X i
  let G₀ : MvPolynomial I K := 1
  let Param₁ (c : C₁) := RationalKernelExtension.Parameters I c.2
  let F₁ (c : C₁) := RationalKernelExtension.numerator F₀ G₀ A c.1 c.2
  let G₁ (c : C₁) := RationalKernelExtension.denominator F₀ G₀ A c.1 c.2
  let Param (c : C₁ × C₂) := RationalKernelExtension.Parameters (Param₁ c.1) c.2.2
  let N (c : C₁ × C₂) := RationalKernelExtension.numerator (F₁ c.1) (G₁ c.1) B c.2.1 c.2.2
  let D (c : C₁ × C₂) := RationalKernelExtension.denominator (F₁ c.1) (G₁ c.1) B c.2.1 c.2.2
  let F (c : C₁ × C₂) : Fin l → MvPolynomial (Param c) K :=
    fun j => N c (Sum.inr j)
  let Free (c : C₁ × C₂) := SubspaceCharts.Outside c.1.2 ⊕ SubspaceCharts.Outside c.2.2
  let S (c : C₁ × C₂) := MvPolynomial (Free c) R
  let coords (c : C₁ × C₂) : Param c → S c :=
    Sum.elim (Sum.elim (fun i => C (base i)) (fun j => X (Sum.inl j)))
      (fun j => X (Sum.inr j))
  let σ (c : C₁ × C₂) : MvPolynomial (Param c) K →ₐ[K] S c := aeval (coords c)
  have hdim (c : C₁ × C₂) : trdeg K (S c) < Fintype.card (Fin l) := by
    have hrn : r ≤ n := by simpa using Fintype.card_le_of_injective c.1.2 c.1.2.injective
    have hsl : s ≤ l := by simpa using Fintype.card_le_of_injective c.2.2 c.2.2.injective
    have hfree : Fintype.card (Free c) = (n-r)+(l-s) := by
      simp only [Free,Fintype.card_sum,SubspaceCharts.card_outside]
    change trdeg K (MvPolynomial (Free c) R) < _
    rw [trdeg_polynomial,hfree,Fintype.card_fin]
    calc
      trdeg K R + ↑((n-r)+(l-s)) ≤ (g : Cardinal) + ↑((n-r)+(l-s)) := add_le_add htr le_rfl
      _ = ↑(g+((n-r)+(l-s))) := (Nat.cast_add _ _).symm
      _ < ↑l := by exact_mod_cast (show g+((n-r)+(l-s)) < l by omega)
  choose P hP havoid using fun c =>
    exists_equation_for_restricted_chart (F c) (D c) (σ c) (hdim c)
  refine ⟨∏ c, P c, Finset.prod_ne_zero_iff.mpr (fun c _ => hP c), ?_⟩
  intro φ x y hr hs hx hy
  let t : I → K := fun i => φ (base i)
  have hbase : rationalMap F₀ G₀ t = t := by ext i; simp [rationalMap,F₀,G₀]
  have hG₀ : eval t G₀ ≠ 0 := by simp [G₀]
  obtain ⟨u₁,v₁,p₁,hkeep₁,hp₁,he₁⟩ := RationalKernelExtension.cover F₀ G₀ A t hG₀
    (by simpa only [hbase] using hr) x (by simpa only [hbase] using hx)
  let c₁ : C₁ := (u₁,v₁)
  have he₁' : rationalMap (F₁ c₁) (G₁ c₁) p₁ = Sum.elim t x := by
    simpa only [hbase] using he₁
  obtain ⟨u₂,v₂,p₂,hkeep₂,hp₂,he₂⟩ := RationalKernelExtension.cover (F₁ c₁) (G₁ c₁) B p₁ hp₁
    (by simpa only [he₁'] using hs) y (by simpa only [he₁'] using hy)
  let c : C₁ × C₂ := (c₁,(u₂,v₂))
  let free : Free c → K := Sum.elim (fun j => p₂ (Sum.inl (Sum.inr j)))
    (fun j => p₂ (Sum.inr j))
  let ψ : S c →ₐ[K] K := aevalTower φ free
  have hcoords : ∀ i, ψ (σ c (X i)) = p₂ i := by
    intro i
    rcases i with (i|j)|j
    · change (aevalTower φ free) ((aeval (coords c)) (X (Sum.inl (Sum.inl i)))) = _
      simp only [aeval_X,coords,Sum.elim_inl,aevalTower_C]
      exact ((hkeep₂ (Sum.inl i)).trans (hkeep₁ i)).symm
    · change (aevalTower φ free) ((aeval (coords c)) (X (Sum.inl (Sum.inr j)))) = _
      rw [aeval_X]
      exact aevalTower_X φ free (Sum.inl j)
    · change (aevalTower φ free) ((aeval (coords c)) (X (Sum.inr j))) = _
      rw [aeval_X]
      exact aevalTower_X φ free (Sum.inr j)
  have he : rationalMap (F c) (D c) p₂ = y := by
    funext j
    have h := congrFun he₂ (Sum.inr j)
    simpa only [rationalMap,F,N,D,c,Sum.elim_inr] using h
  have hzero := havoid c ψ p₂ hcoords hp₂
  rw [he] at hzero
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) hzero

end TwoStage

section Components
variable [IsNoetherianRing R] {I : Type} {a b n l r s g : ℕ}

/-- Finitely many irreducible components suffice; no rational chart on a
component is required. Every actual algebra point factors through one of
these prime quotients. -/
theorem equation_second_stage_components
    (base : I → R)
    (htr : ∀ p ∈ minimalPrimes R, trdeg K (R ⧸ p) ≤ g)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g+n < r+s) :
    ∃ P : MvPolynomial (Fin l) K, P ≠ 0 ∧
      ∀ (φ : R →ₐ[K] K) (x : Fin n → K) (y : Fin l → K),
        r ≤ (evaluated A (fun i => φ (base i))).rank →
        s ≤ (evaluated B (Sum.elim (fun i => φ (base i)) x)).rank →
        evaluated A (fun i => φ (base i)) *ᵥ x = 0 →
        evaluated B (Sum.elim (fun i => φ (base i)) x) *ᵥ y = 0 →
        eval y P = 0 := by
  classical
  let Comp := {p : Ideal R // p ∈ minimalPrimes R}
  let : Fintype Comp := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  have hone (p : Comp) :
      ∃ P : MvPolynomial (Fin l) K, P ≠ 0 ∧
        ∀ (φ : (R ⧸ p.val) →ₐ[K] K) (x : Fin n → K) (y : Fin l → K),
          r ≤ (evaluated A (fun i => φ (Ideal.Quotient.mk p.val (base i)))).rank →
          s ≤ (evaluated B (Sum.elim (fun i => φ (Ideal.Quotient.mk p.val (base i))) x)).rank →
          evaluated A (fun i => φ (Ideal.Quotient.mk p.val (base i))) *ᵥ x = 0 →
          evaluated B (Sum.elim (fun i => φ (Ideal.Quotient.mk p.val (base i))) x) *ᵥ y = 0 →
          eval y P = 0 := by
    let : p.val.IsPrime := p.property.1.1
    exact equation_second_stage (fun i => Ideal.Quotient.mk p.val (base i))
      (htr p.val p.property) A B hcount
  choose P hP h using hone
  refine ⟨∏ p, P p, Finset.prod_ne_zero_iff.mpr (fun p _ => hP p), ?_⟩
  intro φ x y hr hs hx hy
  let : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime φ.toRingHom
  obtain ⟨p,hp,hpker⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal R) ≤ RingHom.ker φ.toRingHom)
  let c : Comp := ⟨p,hp⟩
  let ψ : (R ⧸ p) →ₐ[K] K := Ideal.Quotient.liftₐ p φ (fun z hz => hpker hz)
  have he (z : R) : ψ (Ideal.Quotient.mk p z) = φ z := rfl
  have hz : eval y (P c) = 0 := by
    apply h c ψ x y
    · simpa only [c,he] using hr
    · simpa only [c,he] using hs
    · simpa only [c,he] using hx
    · simpa only [c,he] using hy
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) hz

/-- A nonempty principal open in the second-stage parameters excludes
both equations for every base point and every first-stage vector. -/
theorem principal_open_second_stage [Infinite K]
    (base : I → R)
    (htr : ∀ p ∈ minimalPrimes R, trdeg K (R ⧸ p) ≤ g)
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (B : Matrix (Fin b) (Fin l) (MvPolynomial (I ⊕ Fin n) K))
    (hcount : g+n < r+s) :
    ∃ P : MvPolynomial (Fin l) K,
      (∃ y : Fin l → K, eval y P ≠ 0) ∧
      ∀ y, eval y P ≠ 0 → ∀ (φ : R →ₐ[K] K) (x : Fin n → K),
        let t := fun i => φ (base i)
        r ≤ (evaluated A t).rank →
        s ≤ (evaluated B (Sum.elim t x)).rank →
        evaluated A t *ᵥ x ≠ 0 ∨ evaluated B (Sum.elim t x) *ᵥ y ≠ 0 := by
  obtain ⟨P,hP,h⟩ := equation_second_stage_components base htr A B hcount
  refine ⟨P,PolynomialImageAvoidance.exists_eval_ne_zero hP,?_⟩
  intro y hy φ x
  dsimp only
  intro hr hs
  by_contra! hbad
  exact hy (h φ x y hr hs hbad.1 hbad.2)

end Components
end Quartic.AlgebraicKernelAvoidance
