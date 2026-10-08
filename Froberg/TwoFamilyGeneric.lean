import Froberg.TwoFamilyCharts

/-! Simultaneous incidence for two coefficient families, with their exact
separate span costs and one common projective scaling. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic Quartic.ProjectiveTupleCharts Quartic.ProjectiveKernelIncidence
variable {K V W : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {a₁ a₂ q₁ q₂ : ℕ}

/-- The locus with both coefficient families nonzero is excluded on one
nonempty principal open under the exact two-span incidence budget. -/
theorem two_family_nonzero_open
    (B : ((Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K)) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ F₁ F₂, F₁ ≠ 0 → F₂ ≠ 0 →
      let d₁ := finrank K (tupleSpan F₁)
      let d₂ := finrank K (tupleSpan F₂)
      d₁*(a₁-d₁)+q₁*d₁+d₂*(a₂-d₂)+q₂*d₂ ≤ finrank K (B (F₁,F₂)).range) :
    ∃ D : MvPolynomial (Fin (finrank K V)) K, (∃ x, eval x D ≠ 0) ∧
      ∀ x, eval x D ≠ 0 → ∀ F₁ F₂, F₁ ≠ 0 → F₂ ≠ 0 →
        B (F₁,F₂) ((Module.finBasis K V).equivFun.symm x) ≠ 0 := by
  classical
  let C := (d₁ : Fin (a₁+1)) × (d₂ : Fin (a₂+1)) ×
    (ChartType a₁ q₁ d₁.val × ChartType a₂ q₂ d₂.val)
  have hlocal (c : C) := twoTuple_chart_avoidance B c.2.2.1 c.2.2.2
  choose D hD hgood using hlocal
  have hnz (c : C) : D c ≠ 0 := by
    obtain ⟨x,hx⟩ := hD c
    intro h
    simp [h] at hx
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hnz
  refine ⟨∏ c, D c,⟨x,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun c _ => hx c)
  intro x hx F₁ F₂ hF₁ hF₂ hz
  let d₁ := finrank K (tupleSpan F₁)
  let d₂ := finrank K (tupleSpan F₂)
  have hd₁ : 0 < d₁ := tupleSpan_pos F₁ hF₁
  have hd₂ : 0 < d₂ := tupleSpan_pos F₂ hF₂
  have hda₁ : d₁ ≤ a₁ := by simpa [d₁] using (tupleSpan F₁).finrank_le
  have hda₂ : d₂ ≤ a₂ := by simpa [d₂] using (tupleSpan F₂).finrank_le
  obtain ⟨c₁,c₂,p,s,hs,hF⟩ := cover_two_nonzero_tuples F₁ F₂ hd₁ hd₂ rfl rfl
  let c : C := ⟨⟨d₁,by omega⟩,⟨d₂,by omega⟩,c₁,c₂⟩
  have hx' : eval x (D c) ≠ 0 := by
    have hh : ∏ c, eval x (D c) ≠ 0 := by simpa only [map_prod] using hx
    exact Finset.prod_ne_zero_iff.mp hh c (Finset.mem_univ _)
  have hb := hbound F₁ F₂ hF₁ hF₂
  dsimp only at hb
  rw [hF,map_smul,LinearMap.range_smul _ s hs] at hb
  apply hgood c x hx' p hb
  rw [hF,map_smul,LinearMap.smul_apply] at hz
  exact (smul_eq_zero.mp hz).resolve_left hs

/-- Exact two-family coefficient incidence, including loci where either
family of relation coefficients is zero. -/
theorem two_family_generic_injective
    (B : ((Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K)) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ F : (Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K), F ≠ 0 →
      let d₁ := finrank K (tupleSpan F.1)
      let d₂ := finrank K (tupleSpan F.2)
      d₁*(a₁-d₁)+q₁*d₁+d₂*(a₂-d₂)+q₂*d₂ ≤ finrank K (B F).range) :
    ∃ D : MvPolynomial (Fin (finrank K V)) K, (∃ x, eval x D ≠ 0) ∧
      ∀ x, eval x D ≠ 0 → Function.Injective (B.flip ((Module.finBasis K V).equivFun.symm x)) := by
  classical
  let left := B.comp (LinearMap.inl K (Fin q₁ → Fin a₁ → K) (Fin q₂ → Fin a₂ → K))
  let right := B.comp (LinearMap.inr K (Fin q₁ → Fin a₁ → K) (Fin q₂ → Fin a₂ → K))
  obtain ⟨D₁,hD₁,hleft⟩ := BilinearGeneric.generic_injective left (by
    intro F hF
    have hn : (F,(0 : Fin q₂ → Fin a₂ → K)) ≠ 0 := by
      intro h
      exact hF (congrArg Prod.fst h)
    have hh := hbound (F,0) hn
    have hzero : tupleSpan (0 : Fin q₂ → Fin a₂ → K)=⊥ := by
      apply Submodule.span_eq_bot.mpr
      rintro x ⟨i,rfl⟩
      rfl
    dsimp only at hh
    rw [hzero] at hh
    simpa [left,tupleSpan] using hh)
  obtain ⟨D₂,hD₂,hright⟩ := BilinearGeneric.generic_injective right (by
    intro F hF
    have hn : ((0 : Fin q₁ → Fin a₁ → K),F) ≠ 0 := by
      intro h
      exact hF (congrArg Prod.snd h)
    have hh := hbound (0,F) hn
    have hzero : tupleSpan (0 : Fin q₁ → Fin a₁ → K)=⊥ := by
      apply Submodule.span_eq_bot.mpr
      rintro x ⟨i,rfl⟩
      rfl
    dsimp only at hh
    rw [hzero] at hh
    simpa [right,tupleSpan] using hh)
  obtain ⟨D₃,hD₃,hboth⟩ := two_family_nonzero_open B (by
    intro F₁ F₂ h₁ h₂
    apply hbound (F₁,F₂)
    intro h
    exact h₁ (congrArg Prod.fst h))
  let D : Fin 3 → MvPolynomial (Fin (finrank K V)) K := ![D₁,D₂,D₃]
  have hne : ∀ i, D i ≠ 0 := by
    intro i
    fin_cases i
    · obtain ⟨x,hx⟩ := hD₁
      intro h
      exact hx (by simpa [D] using congrArg (eval x) h)
    · obtain ⟨x,hx⟩ := hD₂
      intro h
      exact hx (by simpa [D] using congrArg (eval x) h)
    · obtain ⟨x,hx⟩ := hD₃
      intro h
      exact hx (by simpa [D] using congrArg (eval x) h)
  obtain ⟨x,hx⟩ := nonempty_principal_intersection D hne
  refine ⟨∏ i, D i,⟨x,?_⟩,?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  intro x hx
  have hxi : ∀ i, eval x (D i) ≠ 0 := by
    simpa only [map_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,forall_const] using hx
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨F₁,F₂⟩ hz
  by_cases h₁ : F₁ = 0
  · subst F₁
    have hh : right.flip ((Module.finBasis K V).equivFun.symm x) F₂ = 0 := hz
    have hi := hright x (by simpa [D] using hxi 1)
    have h₂ : F₂ = 0 := hi (hh.trans (map_zero _).symm)
    simp [h₂]
  by_cases h₂ : F₂ = 0
  · subst F₂
    have hh : left.flip ((Module.finBasis K V).equivFun.symm x) F₁ = 0 := hz
    have hi := hleft x (by simpa [D] using hxi 0)
    have h₁' : F₁ = 0 := hi (hh.trans (map_zero _).symm)
    simp [h₁']
  exact False.elim (hboth x (by simpa [D] using hxi 2) F₁ F₂ h₁ h₂ hz)

end Froberg
