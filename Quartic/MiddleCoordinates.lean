module

public import Quartic.MiddleGeneric

@[expose] public section

/-!
# Generic middle multiplication on the actual `Fin m` child variables

Polynomial renaming transports the proved paired/residual specializations to
`Forms K m d`. Determinant certificates are transported by linear polynomial
substitution on explicit monomial coordinates. Both numerical regimes use the
proved witnesses; no rank or genericity hypothesis replaces their construction.
-/

noncomputable section
namespace Quartic.MiddleCoordinates
open Module MvPolynomial
set_option maxHeartbeats 2000000

variable (K : Type*) [Field K] (m c q : ℕ)
abbrev Mixed := Fin 3 → Forms K m 1
abbrev Target := Forms K m 2 × Forms K m 2
abbrev Parameters := (Fin c → Mixed K m) × (Fin q → Forms K m 2)
abbrev Domain := (Fin c → Mixed K m) × (Fin q → K × K)
/-- Monomial coefficients of all mixed generators and all child quadrics. -/
abbrev CoefficientIndex :=
  (Fin c × Fin 3 × Sym (Fin m) 1) ⊕ (Fin q × Sym (Fin m) 2)
variable {K m c q}

def mulLinear (g : Forms K m 1) : Forms K m 1 →ₗ[K] Forms K m 2 where
  toFun a := ⟨g.val * a.val, g.property.mul a.property⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

/-- Product reduced in the fixed pure-block coordinates `(u,v)`. -/
def projectedProduct (g : Mixed K m) : Mixed K m →ₗ[K] Target K m :=
  (((mulLinear (g 0)).comp (LinearMap.proj (0 : Fin 3))) -
    ((mulLinear (g 2)).comp (LinearMap.proj (2 : Fin 3)))).prod
  (((mulLinear (g 1)).comp (LinearMap.proj (1 : Fin 3))) -
    ((mulLinear (g 2)).comp (LinearMap.proj (2 : Fin 3))))

def multiplication (g : Fin c → Mixed K m) : (Fin c → Mixed K m) →ₗ[K] Target K m :=
  ∑ i : Fin c, (projectedProduct (g i)).comp (LinearMap.proj i)

def childMap (h : Fin q → Forms K m 2) : (Fin q → K × K) →ₗ[K] Target K m where
  toFun a := (∑ i, (a i).1 • h i, ∑ i, (a i).2 • h i)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' s a := by simp [smul_smul, Finset.smul_sum]

def combined (p : Parameters K m c q) : Domain K m c q →ₗ[K] Target K m :=
  (multiplication p.1).coprod (childMap p.2)

/-- The actual quotient middle map for an arbitrary child quadratic subspace. -/
def quotientMap (g : Fin c → Mixed K m) (Q : Submodule K (Forms K m 2)) :
    (Fin c → Mixed K m) →ₗ[K] (Forms K m 2 ⧸ Q) × (Forms K m 2 ⧸ Q) :=
  (Q.mkQ.prodMap Q.mkQ).comp (multiplication g)

def decodeWithBases {U V I J : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (e₁ : U ≃ₗ[K] (I → K)) (e₂ : V ≃ₗ[K] (J → K)) :
    (((Fin c × Fin 3 × I) ⊕ (Fin q × J)) → K) ≃ₗ[K]
      ((Fin c → Fin 3 → U) × (Fin q → V)) where
  toFun a := (fun i d => e₁.symm (fun j => a (Sum.inl (i, d, j))),
    fun i => e₂.symm (fun j => a (Sum.inr (i, j))))
  invFun p := Sum.elim (fun s => e₁ (p.1 s.1 s.2.1) s.2.2)
    (fun s => e₂ (p.2 s.1) s.2)
  left_inv a := by
    funext i
    cases i with
    | inl s => exact congrFun (e₁.apply_symm_apply (fun j => a (Sum.inl (s.1, s.2.1, j)))) s.2.2
    | inr s => exact congrFun (e₂.apply_symm_apply (fun j => a (Sum.inr (s.1, j)))) s.2
  right_inv p := by
    apply Prod.ext
    · funext i d
      exact e₁.symm_apply_apply (p.1 i d)
    · funext i
      exact e₂.symm_apply_apply (p.2 i)
  map_add' a b := by
    apply Prod.ext
    · funext i d
      exact e₁.symm.map_add _ _
    · funext i
      exact e₂.symm.map_add _ _
  map_smul' s a := by
    apply Prod.ext
    · funext i d
      exact e₁.symm.map_smul s _
    · funext i
      exact e₂.symm.map_smul s _

/-- Explicit monomial coordinates parametrize every ordered polynomial family. -/
def decode : (CoefficientIndex m c q → K) ≃ₗ[K] Parameters K m c q :=
  decodeWithBases (formsBasis K m 1).equivFun (formsBasis K m 2).equivFun

/-- The generic statement is on actual `Fin m` coefficients and child quotients. -/
def GenericMiddle (K : Type*) [Field K] (m c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex m c q) K,
    (∃ a₀, eval a₀ D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
      LinearIndependent K (decode a).1 ∧ LinearIndependent K (decode a).2 ∧
      Function.Surjective (quotientMap (decode a).1 (Submodule.span K (Set.range (decode a).2)))

theorem childMap_quotient_zero (h : Fin q → Forms K m 2) (b : Fin q → K × K) :
    let Q := Submodule.span K (Set.range h)
    (Q.mkQ.prodMap Q.mkQ) (childMap h b) = 0 := by
  let Q := Submodule.span K (Set.range h)
  have hmem (i : Fin q) : h i ∈ Q := Submodule.subset_span ⟨i, rfl⟩
  apply Prod.ext
  · apply (Submodule.Quotient.mk_eq_zero Q).mpr
    change (∑ i, (b i).1 • h i) ∈ Q
    exact Q.sum_mem (fun i _ => Q.smul_mem _ (hmem i))
  · apply (Submodule.Quotient.mk_eq_zero Q).mpr
    change (∑ i, (b i).2 • h i) ∈ Q
    exact Q.sum_mem (fun i _ => Q.smul_mem _ (hmem i))

/-- A full-rank combined map surjects onto both actual child quotients. -/
theorem combined_quotient_surjective (p : Parameters K m c q)
    (hs : Function.Surjective (combined p)) :
    Function.Surjective (quotientMap p.1 (Submodule.span K (Set.range p.2))) := by
  let Q := Submodule.span K (Set.range p.2)
  rintro ⟨a, b⟩
  obtain ⟨a, rfl⟩ := Q.mkQ_surjective a
  obtain ⟨b, rfl⟩ := Q.mkQ_surjective b
  obtain ⟨⟨s, t⟩, hst⟩ := hs (a, b)
  refine ⟨s, ?_⟩
  have h := congrArg (Q.mkQ.prodMap Q.mkQ) hst
  change (Q.mkQ.prodMap Q.mkQ) (multiplication p.1 s + childMap p.2 t) = _ at h
  rw [map_add, childMap_quotient_zero, add_zero] at h
  exact h

/-- Surjectivity before taking quotients works for every child subspace. -/
theorem quotient_surjective_of_multiplication (g : Fin c → Mixed K m)
    (hs : Function.Surjective (multiplication g)) (Q : Submodule K (Forms K m 2)) :
    Function.Surjective (quotientMap g Q) := by
  rintro ⟨a, b⟩
  obtain ⟨a, rfl⟩ := Q.mkQ_surjective a
  obtain ⟨b, rfl⟩ := Q.mkQ_surjective b
  obtain ⟨s, hs⟩ := hs (a, b)
  refine ⟨s, ?_⟩
  change (Q.mkQ.prodMap Q.mkQ) (multiplication g s) = _
  rw [hs]
  rfl

/-- Substitute the coordinate linear forms of an actual parameter map. -/
def substituteLinear {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (F : (τ → K) →ₗ[K] (ι → K)) : MvPolynomial ι K →ₐ[K] MvPolynomial τ K :=
  MvPolynomial.aeval (fun i => Quartic.polynomialOfLinear ((LinearMap.proj i).comp F))

theorem eval_substituteLinear {ι τ : Type*} [Fintype τ] [DecidableEq τ]
    (F : (τ → K) →ₗ[K] (ι → K)) (a : τ → K) (D : MvPolynomial ι K) :
    eval a (substituteLinear F D) = eval (F a) D := by
  have hh : (MvPolynomial.aeval a).comp (substituteLinear F) = MvPolynomial.aeval (F a) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, substituteLinear, aeval_X]
    exact Quartic.eval_polynomialOfLinear ((LinearMap.proj i).comp F) a
  exact congrArg (fun f : MvPolynomial ι K →ₐ[K] K => f D) hh

section Rename
variable {a w : ℕ}

/-- The split variable labels have the required number of actual child variables. -/
def variableEquiv (h : 2*a+w=m) : SplitMiddle22.Vars a w ≃ Fin m :=
  (Fintype.equivFin _).trans (finCongr (by simp [SplitMiddle22.Vars]; omega))

/-- Renaming variables restricts to the actual homogeneous polynomial components. -/
def formsRename (e : SplitMiddle22.Vars a w ≃ Fin m) (d : ℕ) :
    homogeneousSubmodule (SplitMiddle22.Vars a w) K d ≃ₗ[K] Forms K m d where
  toFun f := ⟨MvPolynomial.rename e f.val, f.property.rename_isHomogeneous⟩
  invFun f := ⟨MvPolynomial.rename e.symm f.val, f.property.rename_isHomogeneous⟩
  left_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.renameEquiv K e).symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.renameEquiv K e).apply_symm_apply f.val
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' s f := Subtype.ext (by simp)

@[simp] theorem formsRename_val (e : SplitMiddle22.Vars a w ≃ Fin m) (d : ℕ)
    (f : homogeneousSubmodule (SplitMiddle22.Vars a w) K d) :
    (formsRename e d f).val = MvPolynomial.rename e f.val := rfl

def mixedRename (e : SplitMiddle22.Vars a w ≃ Fin m) :
    MiddleGeneric.Mixed K a w ≃ₗ[K] Mixed K m :=
  LinearEquiv.piCongrRight (fun _ : Fin 3 => formsRename e 1)

def familyRename (e : SplitMiddle22.Vars a w ≃ Fin m) :
    (Fin c → MiddleGeneric.Mixed K a w) ≃ₗ[K] (Fin c → Mixed K m) :=
  LinearEquiv.piCongrRight (fun _ : Fin c => mixedRename e)

def childRename (e : SplitMiddle22.Vars a w ≃ Fin m) :
    (Fin q → SplitMiddle22.Quad K a w) ≃ₗ[K] (Fin q → Forms K m 2) :=
  LinearEquiv.piCongrRight (fun _ : Fin q => formsRename e 2)

def parameterRename (e : SplitMiddle22.Vars a w ≃ Fin m) :
    MiddleGeneric.Parameters K a w c q ≃ₗ[K] Parameters K m c q :=
  (familyRename e).prodCongr (childRename e)

def domainRename (e : SplitMiddle22.Vars a w ≃ Fin m) :
    MiddleGeneric.Domain K a w c q ≃ₗ[K] Domain K m c q :=
  (familyRename e).prodCongr (LinearEquiv.refl K _)

def targetRename (e : SplitMiddle22.Vars a w ≃ Fin m) :
    SplitMiddle22.Target K a w ≃ₗ[K] Target K m :=
  (formsRename e 2).prodCongr (formsRename e 2)

/-- Polynomial renaming intertwines actual reduced products. -/
theorem projectedProduct_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (g b : MiddleGeneric.Mixed K a w) :
    targetRename e (SplitMiddle22.projectedProduct g b) =
      projectedProduct (mixedRename e g) (mixedRename e b) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [targetRename, mixedRename, formsRename, projectedProduct, mulLinear,
      SplitMiddle22.projectedProduct, SplitMiddle22.mulLinear]

theorem multiplication_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (g b : Fin c → MiddleGeneric.Mixed K a w) :
    targetRename e (MiddleGeneric.multiplication g b) =
      multiplication (familyRename e g) (familyRename e b) := by
  simp only [MiddleGeneric.multiplication, multiplication, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact projectedProduct_rename e (g i) (b i)

theorem childMap_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (h : Fin q → SplitMiddle22.Quad K a w) (b : Fin q → K × K) :
    targetRename e (MiddleGeneric.childMap h b) = childMap (childRename e h) b := by
  apply Prod.ext <;>
    simp [targetRename, childRename, MiddleGeneric.childMap, childMap]

theorem combined_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (p : MiddleGeneric.Parameters K a w c q) (b : MiddleGeneric.Domain K a w c q) :
    targetRename e (MiddleGeneric.combined p b) = combined (parameterRename e p) (domainRename e b) := by
  change targetRename e (MiddleGeneric.multiplication p.1 b.1 + MiddleGeneric.childMap p.2 b.2) = _
  rw [map_add, multiplication_rename, childMap_rename]
  rfl

/-- The transported polynomial map retains its proved surjectivity. -/
theorem combined_surjective_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (p : MiddleGeneric.Parameters K a w c q) (hp : Function.Surjective (MiddleGeneric.combined p)) :
    Function.Surjective (combined (parameterRename e p)) := by
  intro y
  obtain ⟨b, hb⟩ := hp ((targetRename e).symm y)
  refine ⟨domainRename e b, ?_⟩
  rw [← combined_rename, hb, LinearEquiv.apply_symm_apply]

/-- The parameter change maps explicit actual-variable coefficients to the
finite coordinates of the already constructed determinant certificate. -/
def coordinateChange (e : SplitMiddle22.Vars a w ≃ Fin m) :
    (CoefficientIndex m c q → K) ≃ₗ[K] (MiddleGeneric.ParameterIndex K a w c q → K) :=
  decode.trans ((parameterRename e).symm.trans MiddleGeneric.decode.symm)

theorem coordinateChange_decode (e : SplitMiddle22.Vars a w ≃ Fin m)
    (x : CoefficientIndex m c q → K) :
    parameterRename e (MiddleGeneric.decode (coordinateChange e x)) = decode x := by
  simp only [coordinateChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- Nonempty determinant opens transport to the actual monomial coefficients. -/
theorem genericMiddle_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (hg : MiddleGeneric.GenericMiddle K a w c q) : GenericMiddle K m c q := by
  classical
  obtain ⟨D, ⟨x₀, hx₀⟩, hopen⟩ := hg
  let F := coordinateChange (K := K) (c := c) (q := q) e
  refine ⟨substituteLinear F.toLinearMap D, ?_, ?_⟩
  · refine ⟨F.symm x₀, ?_⟩
    rw [eval_substituteLinear]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hx₀
  · intro x hx
    rw [eval_substituteLinear] at hx
    obtain ⟨h₁, h₂, hs⟩ := hopen (F x) hx
    have he : parameterRename e (MiddleGeneric.decode (F x)) = decode x :=
      coordinateChange_decode e x
    have hi₁ := h₁.map' (mixedRename e).toLinearMap
      (LinearMap.ker_eq_bot.mpr (mixedRename e).injective)
    have hi₂ := h₂.map' (formsRename e 2).toLinearMap
      (LinearMap.ker_eq_bot.mpr (formsRename e 2).injective)
    have hs' := combined_quotient_surjective _ (combined_surjective_rename e _ hs)
    rw [he] at hs'
    refine ⟨?_, ?_, hs'⟩
    · rw [← he]
      exact hi₁
    · rw [← he]
      exact hi₂

/-- Actual multiplication retains surjectivity under variable renaming. -/
theorem multiplication_surjective_rename (e : SplitMiddle22.Vars a w ≃ Fin m)
    (g : Fin c → MiddleGeneric.Mixed K a w)
    (hs : Function.Surjective (MiddleGeneric.multiplication g)) :
    Function.Surjective (multiplication (familyRename e g)) := by
  intro y
  obtain ⟨b, hb⟩ := hs ((targetRename e).symm y)
  refine ⟨familyRename e b, ?_⟩
  rw [← multiplication_rename, hb, LinearEquiv.apply_symm_apply]

end Rename

/-- First numerical regime of the source middle lemma, on actual `Fin m`
variables. The certificate includes independence of both ordered families. -/
theorem genericMiddle_of_first_regime
    (hc_lo : (m + 1) / 2 ≤ c) (hc_hi : c ≤ 3 * m)
    (hq : q ≤ (m + 1).choose 2) : GenericMiddle K m c q := by
  have he : 2 * (m / 2) + m % 2 = m := by omega
  apply genericMiddle_rename (variableEquiv he)
  apply MiddleGeneric.genericMiddle_of_covered_budget
  · omega
  · simpa only [he] using hc_hi
  · simpa only [he] using hq

/-- Second numerical regime, including the exact residual repair budget. -/
theorem genericMiddle_of_second_regime
    (hc : 2 * c ≤ m)
    (hq_lo : c * (m - 2*c) + (m - 2*c + 1).choose 2 ≤ q)
    (hq_hi : q ≤ (m + 1).choose 2) : GenericMiddle K m c q := by
  have he : 2 * c + (m - 2*c) = m := by omega
  apply genericMiddle_rename (variableEquiv he)
  apply MiddleGeneric.genericMiddle_of_repair_budget hq_lo
  simpa only [he] using hq_hi

/-- A nonempty determinant open for either complete numerical budget regime. -/
theorem genericMiddle_of_budgets (hq : q ≤ (m + 1).choose 2)
    (hbudget : ((m + 1) / 2 ≤ c ∧ c ≤ 3*m) ∨
      (2*c ≤ m ∧ c*(m-2*c) + (m-2*c+1).choose 2 ≤ q)) : GenericMiddle K m c q := by
  rcases hbudget with ⟨hlo, hhi⟩ | ⟨hc, hqlo⟩
  · exact genericMiddle_of_first_regime hlo hhi hq
  · exact genericMiddle_of_second_regime hc hqlo hq

/-- In the first regime a single independent mixed family works for every
child quadratic subspace; it already surjects before taking the quotient. -/
theorem first_regime_witness_for_every_quotient
    (hc_lo : (m + 1) / 2 ≤ c) (hc_hi : c ≤ 3 * m) :
    ∃ g : Fin c → Mixed K m, LinearIndependent K g ∧
      Function.Surjective (multiplication g) ∧
      ∀ Q : Submodule K (Forms K m 2), Function.Surjective (quotientMap g Q) := by
  have he : 2 * (m / 2) + m % 2 = m := by omega
  obtain ⟨E, hdim, hfill⟩ := SplitMiddle22.middle_witness_of_covered_budget
    (K := K) (c := m / 2) (w := m % 2) c (by omega) (by simpa only [he] using hc_hi)
  obtain ⟨g, hg, hspan⟩ := MiddleGeneric.family_of_submodule E hdim
  have hs : Function.Surjective (MiddleGeneric.multiplication g) := by
    apply LinearMap.range_eq_top.mp
    rw [MiddleGeneric.range_multiplication, hspan, hfill]
  let e := variableEquiv he
  let g' := familyRename e g
  have hg' : LinearIndependent K g' :=
    hg.map' (mixedRename e).toLinearMap (LinearMap.ker_eq_bot.mpr (mixedRename e).injective)
  have hs' : Function.Surjective (multiplication g') := multiplication_surjective_rename e g hs
  exact ⟨g', hg', hs', quotient_surjective_of_multiplication g' hs'⟩

end Quartic.MiddleCoordinates
