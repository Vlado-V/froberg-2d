module

public import Quartic.ThreeBlockModel
public import Quartic.CorrectionSpace

@[expose] public section

/-!
# The explicit uniform (2,2) middle-block specialization

The child variables are `c` labelled pairs `(tᵢ,wᵢ)` and `w` residual variables.
The mixed generator on each pair is `(x+z)tᵢ+(y+z)wᵢ`. Products are reduced in
the actual coordinates `[x²]=u`, `[y²]=v`, `[z²]=-u-v` of the pure-block quotient.
The proofs below use polynomial products and explicit spanning operations.
-/

noncomputable section
namespace Quartic.SplitMiddle22
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open MvPolynomial Module

variable (K : Type*) [Field K] (c w : ℕ)

abbrev Vars := (Fin c × Fin 2) ⊕ Fin w
abbrev Linear := homogeneousSubmodule (Vars c w) K 1
abbrev Quad := homogeneousSubmodule (Vars c w) K 2
abbrev Source := Fin c → Fin 3 → Linear K c w
abbrev Target := Quad K c w × Quad K c w

variable {K c w}

def tvar (i : Fin c) : Vars c w := Sum.inl (i, 0)
def wvar (i : Fin c) : Vars c w := Sum.inl (i, 1)
def zvar (b : Fin w) : Vars c w := Sum.inr b

def linearVariable (a : Vars c w) : Linear K c w := ⟨X a, isHomogeneous_X K a⟩
def monomial (a b : Vars c w) : Quad K c w :=
  ⟨X a * X b, (isHomogeneous_X K a).mul (isHomogeneous_X K b)⟩

theorem monomial_comm (a b : Vars c w) :
    monomial (K := K) a b = monomial b a := Subtype.ext (mul_comm _ _)

/-- Actual multiplication of homogeneous linear child polynomials. -/
def mulLinear (a : Linear K c w) : Linear K c w →ₗ[K] Quad K c w where
  toFun b := ⟨a.val * b.val, a.property.mul b.property⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

/-- The three actual Y-coefficients of `(x+z)tᵢ+(y+z)wᵢ`. -/
def mixedGenerator (i : Fin c) : Fin 3 → Linear K c w :=
  ![linearVariable (tvar i), linearVariable (wvar i), linearVariable (tvar i) + linearVariable (wvar i)]

/-- Multiplication by one mixed generator, reduced modulo the four pure quadrics. -/
def middleAt (i : Fin c) : (Fin 3 → Linear K c w) →ₗ[K] Target K c w :=
  (((mulLinear (linearVariable (tvar i))).comp (LinearMap.proj (0 : Fin 3))) -
    ((mulLinear (linearVariable (tvar i) + linearVariable (wvar i))).comp (LinearMap.proj (2 : Fin 3)))).prod
  (((mulLinear (linearVariable (wvar i))).comp (LinearMap.proj (1 : Fin 3))) -
    ((mulLinear (linearVariable (tvar i) + linearVariable (wvar i))).comp (LinearMap.proj (2 : Fin 3))))

/-- The full actual middle multiplication for these explicit mixed generators. -/
def middleMap : Source K c w →ₗ[K] Target K c w :=
  ∑ i : Fin c, (middleAt i).comp (LinearMap.proj i)

@[simp] theorem middleMap_single (i : Fin c) (a : Fin 3 → Linear K c w) :
    middleMap (Pi.single i a) = middleAt i a := by
  classical
  simp [middleMap, Pi.single_apply, apply_ite]

def u : Quad K c w →ₗ[K] Target K c w := LinearMap.inl K _ _
def v : Quad K c w →ₗ[K] Target K c w := LinearMap.inr K _ _

@[simp] theorem u_apply (a : Quad K c w) : u a = (a, 0) := rfl
@[simp] theorem v_apply (a : Quad K c w) : v a = (0, a) := rfl

/-- Child quadratic relations can be used in either pure-block coordinate. -/
def filledSpace (Q : Submodule K (Quad K c w)) : Submodule K (Target K c w) :=
  LinearMap.range middleMap ⊔ Q.prod Q

theorem u_t_mem (i : Fin c) (a : Vars c w) :
    u (monomial (K := K) (tvar i) a) ∈ LinearMap.range middleMap := by
  classical
  refine ⟨Pi.single i (Pi.single (0 : Fin 3) (linearVariable a)), ?_⟩
  rw [middleMap_single]
  simp [middleAt, mulLinear, u, linearVariable, monomial]

theorem v_w_mem (i : Fin c) (a : Vars c w) :
    v (monomial (K := K) (wvar i) a) ∈ LinearMap.range middleMap := by
  classical
  refine ⟨Pi.single i (Pi.single (1 : Fin 3) (linearVariable a)), ?_⟩
  rw [middleMap_single]
  simp [middleAt, mulLinear, v, linearVariable, monomial]

/-- The remaining third-column product after subtracting its two known terms. -/
theorem cross_mem (i : Fin c) (a : Vars c w) :
    u (monomial (K := K) (wvar i) a) + v (monomial (tvar i) a) ∈
      LinearMap.range middleMap := by
  classical
  have h : middleAt i (Pi.single (2 : Fin 3) (-linearVariable (K := K) a)) ∈
      LinearMap.range middleMap := ⟨Pi.single i _, middleMap_single i _⟩
  have heq : middleAt i (Pi.single (2 : Fin 3) (-linearVariable (K := K) a)) -
      u (monomial (tvar i) a) - v (monomial (wvar i) a) =
      u (monomial (wvar i) a) + v (monomial (tvar i) a) := by
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [middleAt, mulLinear, linearVariable, monomial] <;> ring
  rw [← heq]
  exact (LinearMap.range middleMap).sub_mem
    ((LinearMap.range middleMap).sub_mem h (u_t_mem i a)) (v_w_mem i a)

/-- Every product between paired variables is filled in the first coordinate. -/
theorem u_active_mem (i j : Fin c) (a b : Fin 2) :
    u (monomial (K := K) (w := w) (Sum.inl (i, a)) (Sum.inl (j, b))) ∈
      LinearMap.range middleMap := by
  fin_cases a
  · exact u_t_mem i _
  · fin_cases b
    · rw [monomial_comm]
      exact u_t_mem j _
    · have h := (LinearMap.range (middleMap (K := K) (c := c) (w := w))).sub_mem
        (cross_mem i (wvar j)) (v_w_mem j (tvar i))
      rw [monomial_comm (tvar i) (wvar j), add_sub_cancel_right] at h
      exact h

/-- Every product between paired variables is filled in the second coordinate. -/
theorem v_active_mem (i j : Fin c) (a b : Fin 2) :
    v (monomial (K := K) (w := w) (Sum.inl (i, a)) (Sum.inl (j, b))) ∈
      LinearMap.range middleMap := by
  fin_cases a
  · fin_cases b
    · have h := (LinearMap.range (middleMap (K := K) (c := c) (w := w))).sub_mem
        (cross_mem i (tvar j)) (u_t_mem j (wvar i))
      rw [monomial_comm (wvar i) (tvar j), add_sub_cancel_left] at h
      exact h
    · rw [monomial_comm]
      exact v_w_mem j _
  · exact v_w_mem i _

theorem u_child_mem (Q : Submodule K (Quad K c w)) (a : Quad K c w) (ha : a ∈ Q) :
    u a ∈ filledSpace Q := Submodule.mem_sup_right ⟨ha, Q.zero_mem⟩

theorem v_child_mem (Q : Submodule K (Quad K c w)) (a : Quad K c w) (ha : a ∈ Q) :
    v a ∈ filledSpace Q := Submodule.mem_sup_right ⟨Q.zero_mem, ha⟩

/-- The single child relation `tᵢz_b` repairs the missing cross-block direction. -/
theorem u_cross_mem (Q : Submodule K (Quad K c w))
    (hQ : ∀ (i : Fin c) (b : Fin w), monomial (tvar i) (zvar b) ∈ Q)
    (i : Fin c) (a : Fin 2) (b : Fin w) :
    u (monomial (Sum.inl (i, a)) (zvar b)) ∈ filledSpace Q := by
  fin_cases a
  · exact Submodule.mem_sup_left (u_t_mem i _)
  · have h := (filledSpace Q).sub_mem (Submodule.mem_sup_left (cross_mem i (zvar b)))
        (v_child_mem Q _ (hQ i b))
    rw [add_sub_cancel_right] at h
    exact h

theorem v_cross_mem (Q : Submodule K (Quad K c w))
    (hQ : ∀ (i : Fin c) (b : Fin w), monomial (tvar i) (zvar b) ∈ Q)
    (i : Fin c) (a : Fin 2) (b : Fin w) :
    v (monomial (Sum.inl (i, a)) (zvar b)) ∈ filledSpace Q := by
  fin_cases a
  · exact v_child_mem Q _ (hQ i b)
  · exact Submodule.mem_sup_left (v_w_mem i _)

/-- All quadratic monomials are filled by the source's explicit repair relations. -/
theorem monomial_mem_filled (Q : Submodule K (Quad K c w))
    (hcross : ∀ (i : Fin c) (b : Fin w), monomial (tvar i) (zvar b) ∈ Q)
    (hresidual : ∀ (a b : Fin w), monomial (zvar a) (zvar b) ∈ Q)
    (a b : Vars c w) :
    u (monomial a b) ∈ filledSpace Q ∧ v (monomial a b) ∈ filledSpace Q := by
  rcases a with ⟨i, a⟩ | a <;> rcases b with ⟨j, b⟩ | b
  · exact ⟨Submodule.mem_sup_left (u_active_mem i j a b), Submodule.mem_sup_left (v_active_mem i j a b)⟩
  · exact ⟨u_cross_mem Q hcross i a b, v_cross_mem Q hcross i a b⟩
  · rw [monomial_comm]
    exact ⟨u_cross_mem Q hcross j b a, v_cross_mem Q hcross j b a⟩
  · exact ⟨u_child_mem Q _ (hresidual a b), v_child_mem Q _ (hresidual a b)⟩

/-- Products of two variables span the actual homogeneous quadratic space. -/
theorem monomials_span :
    Submodule.span K (Set.range (fun ab : Vars c w × Vars c w =>
      monomial (K := K) ab.1 ab.2)) = ⊤ := by
  apply Submodule.map_injective_of_injective
    (Submodule.injective_subtype (Quad K c w))
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  change Submodule.span K (Set.range (fun ab : Vars c w × Vars c w =>
    X ab.1 * X ab.2)) = homogeneousSubmodule (Vars c w) K 2
  rw [← homogeneousSubmodule_one_pow K 2, pow_two,
    homogeneousSubmodule_one_eq_span_X, Submodule.span_mul_span]
  congr 1
  ext p
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨X a, ⟨a, rfl⟩, X b, ⟨b, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    exact ⟨(i, j), rfl⟩

/-- The explicit mixed products and repair quadrics fill the actual complete target. -/
theorem filledSpace_eq_top (Q : Submodule K (Quad K c w))
    (hcross : ∀ (i : Fin c) (b : Fin w), monomial (tvar i) (zvar b) ∈ Q)
    (hresidual : ∀ (a b : Fin w), monomial (zvar a) (zvar b) ∈ Q) :
    filledSpace Q = ⊤ := by
  have hu : ∀ a : Quad K c w, u a ∈ filledSpace Q := by
    have h : (⊤ : Submodule K (Quad K c w)) ≤ (filledSpace Q).comap u := by
      rw [← monomials_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (monomial_mem_filled Q hcross hresidual a b).1
    exact fun a => h Submodule.mem_top
  have hv : ∀ a : Quad K c w, v a ∈ filledSpace Q := by
    have h : (⊤ : Submodule K (Quad K c w)) ≤ (filledSpace Q).comap v := by
      rw [← monomials_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (monomial_mem_filled Q hcross hresidual a b).2
    exact fun a => h Submodule.mem_top
  apply top_unique
  intro a _
  simpa using (filledSpace Q).add_mem (hu a.1) (hv a.2)

/-- The actual middle map after imposing the child quadratic relations. -/
def quotientMiddleMap (Q : Submodule K (Quad K c w)) :
    Source K c w →ₗ[K] (Quad K c w ⧸ Q) × (Quad K c w ⧸ Q) :=
  (Q.mkQ.prodMap Q.mkQ).comp middleMap

/-- Uniform quotient surjectivity for the manuscript's concrete specialization. -/
theorem quotientMiddleMap_surjective (Q : Submodule K (Quad K c w))
    (hcross : ∀ (i : Fin c) (b : Fin w), monomial (tvar i) (zvar b) ∈ Q)
    (hresidual : ∀ (a b : Fin w), monomial (zvar a) (zvar b) ∈ Q) :
    Function.Surjective (quotientMiddleMap Q) := by
  rintro ⟨a, b⟩
  obtain ⟨a, rfl⟩ := Q.mkQ_surjective a
  obtain ⟨b, rfl⟩ := Q.mkQ_surjective b
  have hm : (a, b) ∈ filledSpace Q := by rw [filledSpace_eq_top Q hcross hresidual]; trivial
  obtain ⟨x, ⟨s, rfl⟩, y, hy, heq⟩ := Submodule.mem_sup.mp hm
  refine ⟨s, ?_⟩
  have hzero : (Q.mkQ.prodMap Q.mkQ) y = 0 := by
    apply Prod.ext <;> exact (Submodule.Quotient.mk_eq_zero Q).mpr (by first | exact hy.1 | exact hy.2)
  have h := congrArg (Q.mkQ.prodMap Q.mkQ) heq
  simpa only [map_add, hzero, add_zero, LinearMap.prodMap_apply,
    LinearMap.comp_apply, quotientMiddleMap] using h

/-- Coefficients on distinct paired variables distinguish all mixed generators. -/
theorem mixedGenerator_independent :
    LinearIndependent K (mixedGenerator (K := K) (c := c) (w := w)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have h := congrArg (fun f : Fin 3 → Linear K c w =>
    (f 0).val.coeff (Finsupp.single (tvar i) 1)) ha
  simpa [mixedGenerator, linearVariable, Submodule.coe_sum, Submodule.coe_smul,
    coeff_sum, coeff_smul, coeff_X, Finsupp.single_eq_single_iff, tvar,
    smul_eq_mul, Pi.smul_apply, Finset.sum_apply] using h

/-- A monomial basis for the quadratic child space with its split variable labels. -/
def quadBasis : Basis (Sym (Vars c w) 2) K (Quad K c w) := by
  rw [Quad, homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Vars c w →₀ ℕ | e.degree = 2}).reindex
    (Sym.equivNatSum (Vars c w) 2).symm

instance quadFinite : Module.Finite K (Quad K c w) := Module.Finite.of_basis quadBasis

theorem quad_finrank : Module.finrank K (Quad K c w) = (2 * c + w + 1).choose 2 := by
  rw [Module.finrank_eq_card_basis quadBasis, Sym.card_sym_eq_choose]
  simp [Vars, mul_comm]

/-- Rename a residual quadratic into the full child polynomial ring. -/
def residualQuadrics : Forms K w 2 →ₗ[K] Quad K c w where
  toFun f := ⟨MvPolynomial.rename (zvar (c := c)) f.val, f.property.rename_isHomogeneous⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' a f := Subtype.ext (by simp)

/-- The cross-repair monomials with arbitrary independent scalar coefficients. -/
def crossQuadrics : ((Fin c × Fin w) → K) →ₗ[K] Quad K c w :=
  ∑ a : Fin c × Fin w, (LinearMap.proj a).smulRight (monomial (tvar a.1) (zvar a.2))

/-- The exact repair quadratic family from `tb:middlecount`. -/
def repairMap : (((Fin c × Fin w) → K) × Forms K w 2) →ₗ[K] Quad K c w :=
  crossQuadrics.coprod residualQuadrics

/-- The explicit child quadratic subspace. -/
def repairSpace : Submodule K (Quad K c w) := LinearMap.range repairMap

/-- Erasing paired variables leaves precisely the residual quadratic component. -/
def eraseActive : MvPolynomial (Vars c w) K →ₐ[K] Poly K w :=
  MvPolynomial.aeval (Sum.elim (fun _ => 0) X)

/-- Setting just `tᵢ` to one reads the cross-repair coefficients on its row. -/
def probeActive (i : Fin c) : MvPolynomial (Vars c w) K →ₐ[K] Poly K w :=
  MvPolynomial.aeval (Sum.elim (fun a => if a = (i, 0) then 1 else 0) X)

@[simp] theorem eraseActive_residual (f : Forms K w 2) :
    eraseActive (residualQuadrics (c := c) f).val = f.val := by
  have h : (eraseActive (K := K) (c := c) (w := w)).comp
      (MvPolynomial.rename (zvar (c := c))) = AlgHom.id K (Poly K w) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [eraseActive, zvar]
  exact congrArg (fun h : Poly K w →ₐ[K] Poly K w => h f.val) h

@[simp] theorem eraseActive_cross (a : (Fin c × Fin w) → K) :
    eraseActive (crossQuadrics a).val = 0 := by
  simp [crossQuadrics, monomial, eraseActive, tvar, zvar]

/-- Each scalar coefficient is recovered from a genuine polynomial substitution. -/
theorem probeActive_cross_coeff (a : (Fin c × Fin w) → K) (i : Fin c) (b : Fin w) :
    (probeActive i (crossQuadrics a).val).coeff (Finsupp.single b 1) = a (i, b) := by
  classical
  simp [probeActive, crossQuadrics, monomial, tvar, zvar, coeff_X,
    Finsupp.single_eq_single_iff, Fintype.sum_prod_type, smul_eq_mul, apply_ite]

/-- The repair quadrics are independent, including the full residual quadratic space. -/
theorem repairMap_injective : Function.Injective (repairMap (K := K) (c := c) (w := w)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨a, f⟩ h
  have hf : f = 0 := by
    apply Subtype.ext
    have he := congrArg (fun p : Quad K c w => eraseActive p.val) h
    simpa [repairMap, LinearMap.coprod_apply] using he
  have ha : a = 0 := by
    funext ib
    have he := congrArg (fun p : Quad K c w =>
      (probeActive ib.1 p.val).coeff (Finsupp.single ib.2 1)) h
    simpa [repairMap, LinearMap.coprod_apply, hf, probeActive_cross_coeff] using he
  exact Prod.ext ha hf

/-- This is exactly the numerical repair budget appearing in `tb:middlecount`. -/
theorem repairSpace_finrank :
    Module.finrank K (repairSpace (K := K) (c := c) (w := w)) = c * w + (w + 1).choose 2 := by
  rw [repairSpace, LinearMap.finrank_range_of_inj repairMap_injective]
  simp [Module.finrank_prod, Quartic.finrank_quadrics]

theorem repairSpace_contains_cross (i : Fin c) (b : Fin w) :
    monomial (K := K) (tvar i) (zvar b) ∈ repairSpace := by
  classical
  refine ⟨(Pi.single (i, b) 1, 0), ?_⟩
  simp [repairMap, crossQuadrics, LinearMap.coprod_apply, Pi.single_apply]

theorem repairSpace_contains_residual (a b : Fin w) :
    monomial (K := K) (c := c) (zvar a) (zvar b) ∈ repairSpace := by
  let f : Forms K w 2 := ⟨X a * X b,
    (isHomogeneous_X K a).mul (isHomogeneous_X K b)⟩
  refine ⟨(0, f), ?_⟩
  apply Subtype.ext
  simp [repairMap, residualQuadrics, f, monomial]

/-- Every enlargement of the explicit repair space retains middle surjectivity. -/
theorem quotientMiddleMap_surjective_of_repair_le (Q : Submodule K (Quad K c w))
    (hQ : repairSpace ≤ Q) : Function.Surjective (quotientMiddleMap Q) :=
  quotientMiddleMap_surjective Q
    (fun i b => hQ (repairSpace_contains_cross i b))
    (fun a b => hQ (repairSpace_contains_residual a b))

section Extension
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- Extending an actual subspace to any permitted intermediate dimension. -/
theorem exists_extension_finrank (S : Submodule K V) (q : ℕ)
    (hlo : Module.finrank K S ≤ q) (hhi : q ≤ Module.finrank K V) :
    ∃ Q : Submodule K V, S ≤ Q ∧ Module.finrank K Q = q := by
  have hquot : q - Module.finrank K S ≤ Module.finrank K (V ⧸ S) := by
    rw [Submodule.finrank_quotient]
    omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hquot
  let U : Submodule K (V ⧸ S) := Submodule.span K (Set.range f)
  have hU : Module.finrank K U = q - Module.finrank K S := by
    simpa [U] using finrank_span_eq_card hf
  refine ⟨U.comap S.mkQ, ?_, ?_⟩
  · intro a ha
    change S.mkQ a ∈ U
    rw [show S.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero S).mpr ha]
    exact U.zero_mem
  · rw [CorrectionSpace.finrank_preimage S.mkQ U S.mkQ_surjective,
      Submodule.ker_mkQ, hU]
    omega

end Extension

/-- The source's entire second budget regime has a concrete uniform witness.
The mixed generators are independent, and the child space has the prescribed
exact dimension, with no assumed rank condition. -/
theorem middle_witness_of_budget (q : ℕ)
    (hlo : c * w + (w + 1).choose 2 ≤ q)
    (hhi : q ≤ (2 * c + w + 1).choose 2) :
    LinearIndependent K (mixedGenerator (K := K) (c := c) (w := w)) ∧
    ∃ Q : Submodule K (Quad K c w), Module.finrank K Q = q ∧
      Function.Surjective (quotientMiddleMap Q) := by
  refine ⟨mixedGenerator_independent, ?_⟩
  obtain ⟨Q, hQ, hdim⟩ := exists_extension_finrank (repairSpace (K := K) (c := c) (w := w)) q
    (by simpa [repairSpace_finrank] using hlo) (by simpa [quad_finrank] using hhi)
  exact ⟨Q, hdim, quotientMiddleMap_surjective_of_repair_le Q hQ⟩

/-- An even-dimensional child space requires no repair quadrics at all. -/
theorem even_middle_surjective (Q : Submodule K (Quad K c 0)) :
    Function.Surjective (quotientMiddleMap Q) :=
  quotientMiddleMap_surjective Q (fun _ b => Fin.elim0 b) (fun a => Fin.elim0 a)

/-- One further mixed generator `(x+y)z_b` on every remaining variable. -/
def singletonGenerator (b : Fin w) : Fin 3 → Linear K c w :=
  ![linearVariable (zvar b), linearVariable (zvar b), 0]

def singletonAt (b : Fin w) : (Fin 3 → Linear K c w) →ₗ[K] Target K c w :=
  ((mulLinear (linearVariable (zvar b))).comp (LinearMap.proj (0 : Fin 3))).prod
    ((mulLinear (linearVariable (zvar b))).comp (LinearMap.proj (1 : Fin 3)))

def singletonMap : (Fin w → Fin 3 → Linear K c w) →ₗ[K] Target K c w :=
  ∑ b : Fin w, (singletonAt b).comp (LinearMap.proj b)

/-- Combined actual polynomial map for the paired and singleton generators. -/
def coveredMiddleMap : (Source K c w × (Fin w → Fin 3 → Linear K c w)) →ₗ[K] Target K c w :=
  middleMap.coprod singletonMap

theorem singletonMap_single (b : Fin w) (a : Fin 3 → Linear K c w) :
    singletonMap (Pi.single b a) = singletonAt b a := by
  classical
  simp [singletonMap, Pi.single_apply, apply_ite]

theorem u_residual_mem (b : Fin w) (a : Vars c w) :
    u (monomial (K := K) (zvar b) a) ∈ LinearMap.range singletonMap := by
  classical
  refine ⟨Pi.single b (Pi.single (0 : Fin 3) (linearVariable a)), ?_⟩
  rw [singletonMap_single]
  simp [singletonAt, mulLinear, u, linearVariable, monomial]

theorem v_residual_mem (b : Fin w) (a : Vars c w) :
    v (monomial (K := K) (zvar b) a) ∈ LinearMap.range singletonMap := by
  classical
  refine ⟨Pi.single b (Pi.single (1 : Fin 3) (linearVariable a)), ?_⟩
  rw [singletonMap_single]
  simp [singletonAt, mulLinear, v, linearVariable, monomial]

/-- Including a singleton for each unpaired variable fills every target before
any child relations are imposed. In particular this treats odd child dimension
with exactly `(m+1)/2` mixed generators by taking `w=1`. -/
theorem coveredMiddleMap_surjective :
    Function.Surjective (coveredMiddleMap (K := K) (c := c) (w := w)) := by
  have hleft : LinearMap.range (middleMap (K := K) (c := c) (w := w)) ≤
      LinearMap.range coveredMiddleMap := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(a, 0), by simp [coveredMiddleMap]⟩
  have hright : LinearMap.range (singletonMap (K := K) (c := c) (w := w)) ≤
      LinearMap.range coveredMiddleMap := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(0, a), by simp [coveredMiddleMap]⟩
  have hm (a b : Vars c w) :
      u (monomial (K := K) a b) ∈ LinearMap.range coveredMiddleMap ∧
      v (monomial (K := K) a b) ∈ LinearMap.range coveredMiddleMap := by
    rcases a with ⟨i, a⟩ | a <;> rcases b with ⟨j, b⟩ | b
    · exact ⟨hleft (u_active_mem i j a b), hleft (v_active_mem i j a b)⟩
    · rw [monomial_comm]
      exact ⟨hright (u_residual_mem b _), hright (v_residual_mem b _)⟩
    · exact ⟨hright (u_residual_mem a _), hright (v_residual_mem a _)⟩
    · exact ⟨hright (u_residual_mem a _), hright (v_residual_mem a _)⟩
  have hu : ∀ a : Quad K c w, u a ∈ LinearMap.range coveredMiddleMap := by
    have h : (⊤ : Submodule K (Quad K c w)) ≤ (LinearMap.range coveredMiddleMap).comap u := by
      rw [← monomials_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (hm a b).1
    exact fun a => h Submodule.mem_top
  have hv : ∀ a : Quad K c w, v a ∈ LinearMap.range coveredMiddleMap := by
    have h : (⊤ : Submodule K (Quad K c w)) ≤ (LinearMap.range coveredMiddleMap).comap v := by
      rw [← monomials_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (hm a b).2
    exact fun a => h Submodule.mem_top
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro a _
  simpa using (LinearMap.range coveredMiddleMap).add_mem (hu a.1) (hv a.2)

/-- Passing to any child quadratic quotient preserves this surjectivity. -/
theorem covered_quotient_surjective (Q : Submodule K (Quad K c w)) :
    Function.Surjective ((Q.mkQ.prodMap Q.mkQ).comp coveredMiddleMap) := by
  rintro ⟨a, b⟩
  obtain ⟨a, rfl⟩ := Q.mkQ_surjective a
  obtain ⟨b, rfl⟩ := Q.mkQ_surjective b
  obtain ⟨s, hs⟩ := coveredMiddleMap_surjective (a, b)
  exact ⟨s, by change (Q.mkQ.prodMap Q.mkQ) (coveredMiddleMap s) = _; rw [hs]; rfl⟩

/-- The complete independent family of paired and singleton mixed generators. -/
def coveredGenerators : Fin c ⊕ Fin w → Fin 3 → Linear K c w :=
  Sum.elim mixedGenerator singletonGenerator

theorem coveredGenerators_independent :
    LinearIndependent K (coveredGenerators (K := K) (c := c) (w := w)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  cases i with
  | inl i =>
    have h := congrArg (fun f : Fin 3 → Linear K c w =>
      (f 0).val.coeff (Finsupp.single (tvar i) 1)) ha
    simpa [coveredGenerators, mixedGenerator, singletonGenerator, linearVariable,
      Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul, coeff_X,
      Finsupp.single_eq_single_iff, tvar, zvar, smul_eq_mul, Pi.smul_apply,
      Finset.sum_apply, Fintype.sum_sum_type] using h
  | inr b =>
    have h := congrArg (fun f : Fin 3 → Linear K c w =>
      (f 0).val.coeff (Finsupp.single (zvar b) 1)) ha
    simpa [coveredGenerators, mixedGenerator, singletonGenerator, linearVariable,
      Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul, coeff_X,
      Finsupp.single_eq_single_iff, tvar, zvar, smul_eq_mul, Pi.smul_apply,
      Finset.sum_apply, Fintype.sum_sum_type] using h

/-- Reduction of products for an arbitrary actual mixed polynomial. -/
def projectedProduct (g : Fin 3 → Linear K c w) :
    (Fin 3 → Linear K c w) →ₗ[K] Target K c w :=
  (((mulLinear (g 0)).comp (LinearMap.proj (0 : Fin 3))) -
    ((mulLinear (g 2)).comp (LinearMap.proj (2 : Fin 3)))).prod
  (((mulLinear (g 1)).comp (LinearMap.proj (1 : Fin 3))) -
    ((mulLinear (g 2)).comp (LinearMap.proj (2 : Fin 3))))

/-- Store an actual mixed polynomial as a polynomial in X with child-polynomial coefficients. -/
def mixedPolynomial (g : Fin 3 → Linear K c w) :
    MvPolynomial (Fin 3) (MvPolynomial (Vars c w) K) :=
  C (g 0).val * X 0 + C (g 1).val * X 1 + C (g 2).val * X 2

/-- Universal coefficient calculation for two linear polynomials over any
commutative coefficient ring. -/
theorem reduction_linear_product {R : Type*} [CommRing R] (g a : Fin 3 → R) :
    ThreeBlock.quadraticReduction
      ((C (g 0) * X 0 + C (g 1) * X 1 + C (g 2) * X 2) *
       (C (a 0) * X 0 + C (a 1) * X 1 + C (a 2) * X 2)) =
      ![g 0 * a 0 - g 2 * a 2, g 1 * a 1 - g 2 * a 2] := by
  simp only [C_mul_X_eq_monomial]
  funext i
  fin_cases i <;>
    norm_num [ThreeBlock.quadraticReduction, add_mul, mul_add, monomial_mul_monomial,
      coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]

/-- The coordinate formula is precisely polynomial multiplication followed by
reduction modulo `xy,xz,yz,x²+y²+z²`; it is not an unrelated matrix model. -/
theorem projectedProduct_reduction (g a : Fin 3 → Linear K c w) :
    ThreeBlock.quadraticReduction (mixedPolynomial g * mixedPolynomial a) =
      ![(projectedProduct g a).1.val, (projectedProduct g a).2.val] := by
  simpa [mixedPolynomial, projectedProduct, mulLinear] using
    reduction_linear_product (fun i => (g i).val) (fun i => (a i).val)

theorem middleAt_eq_projectedProduct (i : Fin c) :
    middleAt (K := K) (w := w) i = projectedProduct (mixedGenerator i) := rfl

theorem singletonAt_eq_projectedProduct (b : Fin w) :
    singletonAt (K := K) (c := c) b = projectedProduct (singletonGenerator b) := by
  apply LinearMap.ext
  intro a
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [singletonAt, projectedProduct, singletonGenerator, mulLinear]

/-- Intrinsic multiplication image of an actual subspace of mixed polynomials. -/
def middleImage (E : Submodule K (Fin 3 → Linear K c w)) : Submodule K (Target K c w) :=
  Submodule.span K {p | ∃ g ∈ E, ∃ a, projectedProduct g a = p}

theorem middleImage_mono {E E' : Submodule K (Fin 3 → Linear K c w)} (h : E ≤ E') :
    middleImage E ≤ middleImage E' := by
  apply Submodule.span_mono
  rintro p ⟨g, hg, a, rfl⟩
  exact ⟨g, h hg, a, rfl⟩

theorem range_middleMap_le_image (E : Submodule K (Fin 3 → Linear K c w))
    (hE : ∀ i, mixedGenerator i ∈ E) : LinearMap.range middleMap ≤ middleImage E := by
  rintro p ⟨a, rfl⟩
  simp only [middleMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.subset_span ⟨mixedGenerator i, hE i, a i,
    congrArg (fun f => f (a i)) (middleAt_eq_projectedProduct i).symm⟩

theorem range_singletonMap_le_image (E : Submodule K (Fin 3 → Linear K c w))
    (hE : ∀ b, singletonGenerator b ∈ E) : LinearMap.range singletonMap ≤ middleImage E := by
  rintro p ⟨a, rfl⟩
  simp only [singletonMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Submodule.sum_mem
  intro b _
  exact Submodule.subset_span ⟨singletonGenerator b, hE b, a b,
    congrArg (fun f => f (a b)) (singletonAt_eq_projectedProduct b).symm⟩

/-- The spanning result holds for every enlargement of the mixed-generator space. -/
theorem covered_image_eq_top (E : Submodule K (Fin 3 → Linear K c w))
    (hE : ∀ i, coveredGenerators i ∈ E) : middleImage E = ⊤ := by
  have h : LinearMap.range (coveredMiddleMap (K := K) (c := c) (w := w)) ≤ middleImage E := by
    rintro p ⟨⟨a, b⟩, rfl⟩
    change middleMap a + singletonMap b ∈ middleImage E
    exact (middleImage E).add_mem
      (range_middleMap_le_image E (fun i => hE (Sum.inl i)) ⟨a, rfl⟩)
      (range_singletonMap_le_image E (fun i => hE (Sum.inr i)) ⟨b, rfl⟩)
  rw [LinearMap.range_eq_top.mpr coveredMiddleMap_surjective] at h
  exact top_unique h

/-- A monomial basis for the linear child space. -/
def linearBasis : Basis (Sym (Vars c w) 1) K (Linear K c w) := by
  rw [Linear, homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Vars c w →₀ ℕ | e.degree = 1}).reindex
    (Sym.equivNatSum (Vars c w) 1).symm

instance linearFinite : Module.Finite K (Linear K c w) := Module.Finite.of_basis linearBasis

theorem linear_finrank : Module.finrank K (Linear K c w) = 2 * c + w := by
  rw [Module.finrank_eq_card_basis linearBasis, Sym.card_sym_eq_choose]
  simp [Vars, mul_comm]

/-- The whole first numerical regime has a concrete witness: enlarge the
`c+w` paired/singleton generators to any allowed mixed dimension. Taking
`w=0` or `w=1` gives exactly `ceil(m/2)` initial generators. -/
theorem middle_witness_of_covered_budget (e : ℕ)
    (hlo : c + w ≤ e) (hhi : e ≤ 3 * (2 * c + w)) :
    ∃ E : Submodule K (Fin 3 → Linear K c w),
      Module.finrank K E = e ∧ middleImage E = ⊤ := by
  let S := Submodule.span K (Set.range (coveredGenerators (K := K) (c := c) (w := w)))
  have hS : Module.finrank K S = c + w := by
    simpa [S] using finrank_span_eq_card (coveredGenerators_independent (K := K) (c := c) (w := w))
  have htotal : Module.finrank K (Fin 3 → Linear K c w) = 3 * (2 * c + w) := by
    simp [Module.finrank_pi_fintype, linear_finrank]
  obtain ⟨E, hE, he⟩ := exists_extension_finrank S e (by omega) (by omega)
  refine ⟨E, he, covered_image_eq_top E ?_⟩
  intro i
  exact hE (Submodule.subset_span ⟨i, rfl⟩)

end Quartic.SplitMiddle22
