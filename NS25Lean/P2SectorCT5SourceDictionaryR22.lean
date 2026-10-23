import NS25Lean.P2SectorCCanonicalStaircaseR21
import NS25Lean.P2SectorCCanonicalForwardPacketR14

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NS25Lean.L5A2C4OR22
open FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1
  L5A2C4OR3 L5A2C4OR5 L5A2C4OR6 L5A2C4OR14 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21
variable {Gamma : NumericalSemigroup}

/-- Polynomial minimality uses literal coordinate divisibility. -/
def ChartMinimal (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) : Prop :=
  z ∈ monomialClosure (chartGenerators B e HD) ∧
    ∀ w ∈ monomialClosure (chartGenerators B e HD),
      w.1 ≤ z.1 → w.2.1 ≤ z.2.1 → w.2.2 ≤ z.2.2 → w=z

private theorem cut_add {H : NumericalSemigroup} {m x h : ℕ}
    (hx : x ∈ cyclicCut H m) (hh : h ∈ H) : x+h ∈ cyclicCut H m := by
  obtain ⟨hxH,n,hn,t,ht,heq⟩ := hx
  refine ⟨H.toAddSubmonoid.add_mem hxH hh,n,hn,t+h,H.toAddSubmonoid.add_mem ht hh,?_⟩
  omega

private theorem grid_mem (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r i j : ℕ) : normalizedGrid B e r i j ∈ routingH B e := by
  apply (mem_generatedThree_iff _ _ _ _).mpr
  exact ⟨r,i,j,rfl⟩

/-- Genuine H-minimality expressed without truncated predecessor subtraction. -/
theorem minimalTail_iff_literal (H : NumericalSemigroup) (m x : ℕ) :
    IsMinimalTailGenerator H.toAddSubmonoid (cyclicCut H m) x ↔
      x ∈ cyclicCut H m ∧ ∀ y h : ℕ, y ∈ cyclicCut H m → h ∈ H →
        x=y+h → h=0 := by
  constructor
  · rintro ⟨hx,hmin⟩
    refine ⟨hx,?_⟩
    intro y h hy hh heq
    by_contra h0
    rcases hmin h hh h0 with hlt | hnot
    · omega
    · apply hnot
      simpa [heq] using hy
  · rintro ⟨hx,hmin⟩
    refine ⟨hx,?_⟩
    intro h hh h0
    by_cases hlt : x<h
    · exact Or.inl hlt
    · right
      intro hy
      exact h0 (hmin (x-h) h hy hh (by omega))

/-- The actual three-generator factorization reduces all nonzero H
predecessors to one literal a/b/c predecessor in the actual cut. -/
theorem literal_minimal_of_generator_predecessors
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (n : ℕ)
    (ha : ∀ x, x ∈ cyclicCut (routingH B e) (routingM B e) →
      n ≠ x+routingA B e)
    (hb : ∀ x, x ∈ cyclicCut (routingH B e) (routingM B e) →
      n ≠ x+routingB B e)
    (hc : ∀ x, x ∈ cyclicCut (routingH B e) (routingM B e) →
      n ≠ x+routingC B e) :
    ∀ x h : ℕ, x ∈ cyclicCut (routingH B e) (routingM B e) →
      h ∈ routingH B e → n=x+h → h=0 := by
  intro x h hx hh heq
  obtain ⟨r,i,j,hfac⟩ := routingH_factorization B e hh
  by_cases hr : 0 < r
  · have ht := cut_add hx (grid_mem B e (r-1) i j)
    apply False.elim
    apply ha _ ht
    simp only [normalizedGrid] at ht ⊢
    have hmul := congrArg (fun t => t*routingA B e) (show r-1+1=r by omega)
    simp only [Nat.add_mul,one_mul] at hmul
    omega
  · by_cases hi : 0 < i
    · apply False.elim
      apply hb _ (cut_add hx (grid_mem B e r (i-1) j))
      simp only [normalizedGrid]
      have hmul := congrArg (fun t => t*routingB B e) (show i-1+1=i by omega)
      simp only [Nat.add_mul,one_mul] at hmul
      omega
    · by_cases hj : 0 < j
      · apply False.elim
        apply hc _ (cut_add hx (grid_mem B e r i (j-1)))
        simp only [normalizedGrid]
        have hmul := congrArg (fun t => t*routingC B e) (show j-1+1=j by omega)
        simp only [Nat.add_mul,one_mul] at hmul
        omega
      · have : r=0 ∧ i=0 ∧ j=0 := by omega
        simp [this.1,this.2.1,this.2.2] at hfac
        exact hfac

/-- R14 total inverse lift is an actual necessary lower bound for any
H-predecessor, by canonical Apéry minimality, including hidden wraps. -/
theorem predecessorB_lift_lower_bound (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {r i j x : ℕ}
    (T : CanonicalPredecessorB B e HD i j) (hx : x ∈ routingH B e)
    (heq : normalizedGrid B e r i j=x+routingB B e) : T.predLift ≤ r := by
  by_contra hlt
  have hpos : 0<T.predLift-r := by omega
  have hsub := congrArg (fun t => t*routingA B e)
    (show T.predLift-r+r=T.predLift by omega)
  have hv := T.value
  simp only [normalizedGrid,zero_mul,zero_add,Nat.add_mul] at hv heq hsub
  exact canonical_no_positive_a_subtraction B e HD T.predDomain hpos (by omega) hx

theorem predecessorC_lift_lower_bound (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {r i j x : ℕ}
    (T : CanonicalPredecessorC B e HD i j) (hx : x ∈ routingH B e)
    (heq : normalizedGrid B e r i j=x+routingC B e) : T.predLift ≤ r := by
  by_contra hlt
  have hpos : 0<T.predLift-r := by omega
  have hsub := congrArg (fun t => t*routingA B e)
    (show T.predLift-r+r=T.predLift by omega)
  have hv := T.value
  simp only [normalizedGrid,zero_mul,zero_add,Nat.add_mul] at hv heq hsub
  exact canonical_no_positive_a_subtraction B e HD T.predDomain hpos (by omega) hx

/-- Explicit hidden-b lift from the two actual R14 inverse atlas arms. -/
theorem hiddenB_lift_lower_bound (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {r j x : ℕ}
    (hd : HerzogLShapeDomain HD 0 j) (hx : x ∈ routingH B e)
    (heq : normalizedGrid B e r 0 j=x+routingB B e) :
    (if cr23 HD ≤ j then cr21 HD else c1 B e) ≤ r := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  by_cases hj : cr23 HD ≤ j
  · simp only [hj,ite_true]
    let T : CanonicalPredecessorB B e HD 0 j := {
      predI := c2 B e-1, predJ := j-cr23 HD, predLift := cr21 HD
      predDomain := by unfold HerzogLShapeDomain at *; omega
      value := by
        have hr := (coherent_normalized_relations B e HD).2.1
        have ht := congrArg (fun t => t*routingC B e) (Nat.add_sub_of_le hj)
        have hI := congrArg (fun t => t*routingB B e)
          (show c2 B e-1+1=c2 B e by omega)
        simp only [normalizedGrid,zero_mul,zero_add,add_zero,Nat.add_mul,one_mul] at *
        omega }
    exact predecessorB_lift_lower_bound B e HD T hx heq
  · simp only [hj,ite_false]
    let T : CanonicalPredecessorB B e HD 0 j := {
      predI := cr12 HD-1, predJ := j+cr13 HD, predLift := c1 B e
      predDomain := by unfold HerzogLShapeDomain at *; omega
      value := by
        have hr := (coherent_normalized_relations B e HD).1
        have hI := congrArg (fun t => t*routingB B e)
          (show cr12 HD-1+1=cr12 HD by omega)
        simp only [normalizedGrid,zero_mul,zero_add,add_zero,Nat.add_mul,one_mul] at *
        omega }
    exact predecessorB_lift_lower_bound B e HD T hx heq

theorem hiddenC_lift_lower_bound (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {r i x : ℕ}
    (hd : HerzogLShapeDomain HD i 0) (hx : x ∈ routingH B e)
    (heq : normalizedGrid B e r i 0=x+routingC B e) :
    (if cr32 HD ≤ i then cr31 HD else c1 B e) ≤ r := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  by_cases hi : cr32 HD ≤ i
  · simp only [hi,ite_true]
    let T : CanonicalPredecessorC B e HD i 0 := {
      predI := i-cr32 HD, predJ := c3 B e-1, predLift := cr31 HD
      predDomain := by unfold HerzogLShapeDomain at *; omega
      value := by
        have hr := (coherent_normalized_relations B e HD).2.2
        have ht := congrArg (fun t => t*routingB B e) (Nat.add_sub_of_le hi)
        have hJ := congrArg (fun t => t*routingC B e)
          (show c3 B e-1+1=c3 B e by omega)
        simp only [normalizedGrid,zero_mul,zero_add,add_zero,Nat.add_mul,one_mul] at *
        omega }
    exact predecessorC_lift_lower_bound B e HD T hx heq
  · simp only [hi,ite_false]
    let T : CanonicalPredecessorC B e HD i 0 := {
      predI := i+cr12 HD, predJ := cr13 HD-1, predLift := c1 B e
      predDomain := by unfold HerzogLShapeDomain at *; omega
      value := by
        have hr := (coherent_normalized_relations B e HD).1
        have hJ := congrArg (fun t => t*routingC B e)
          (show cr13 HD-1+1=cr13 HD by omega)
        simp only [normalizedGrid,zero_mul,zero_add,add_zero,Nat.add_mul,one_mul] at *
        omega }
    exact predecessorC_lift_lower_bound B e HD T hx heq

/-- Ordinary predecessors are proper chart divisors. Hidden predecessors
are excluded by their actual R14 lift. These are helper bounds, not fields
or new hypotheses of the final actual source theorem. -/
theorem chartMinimal_literal_of_wrap_bounds {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hd : HerzogLShapeDomain R.HD i j)
    (hmin : ChartMinimal P.M.base R.e R.HD (r,i,j))
    (hb : i=0 → r < if cr23 R.HD ≤ j then cr21 R.HD else c1 P.M.base R.e)
    (hc : j=0 → r < if cr32 R.HD ≤ i then cr31 R.HD else c1 P.M.base R.e) :
    ∀ x h : ℕ, x ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      h ∈ routingH P.M.base R.e →
      normalizedGrid P.M.base R.e r i j=x+h → h=0 := by
  apply literal_minimal_of_generator_predecessors
  · intro x hx heq
    by_cases hr : r=0
    · subst r
      exact canonical_no_positive_a_subtraction P.M.base R.e R.HD hd
        (show 0<1 by omega) (by simpa [normalizedGrid] using heq.symm) hx.1
    · have hxeq : normalizedGrid P.M.base R.e (r-1) i j=x := by
        have hmul := congrArg (fun t => t*routingA P.M.base R.e)
          (show r-1+1=r by omega)
        simp only [normalizedGrid,Nat.add_mul,one_mul] at heq hmul ⊢
        omega
      have hmem := (actual_chart_staircase_iff R hm hn (r-1) i j hd).mp
        (hxeq.symm ▸ hx)
      have hsame := hmin.2 (r-1,i,j) hmem (by dsimp; omega) (by rfl) (by rfl)
      have he := congrArg Prod.fst hsame
      simp only [Prod.fst] at he
      omega
  · intro x hx heq
    by_cases hi : i=0
    · subst i
      have hle := hiddenB_lift_lower_bound P.M.base R.e R.HD hd hx.1 heq
      have hlt := hb rfl
      omega
    · have hd' : HerzogLShapeDomain R.HD (i-1) j := by
        unfold HerzogLShapeDomain at *; omega
      have hxeq : normalizedGrid P.M.base R.e r (i-1) j=x := by
        have hmul := congrArg (fun t => t*routingB P.M.base R.e)
          (show i-1+1=i by omega)
        simp only [normalizedGrid,Nat.add_mul,one_mul] at heq hmul ⊢
        omega
      have hmem := (actual_chart_staircase_iff R hm hn r (i-1) j hd').mp
        (hxeq.symm ▸ hx)
      have hsame := hmin.2 (r,i-1,j) hmem (by rfl) (by dsimp; omega) (by rfl)
      have he := congrArg (fun z : Monomial => z.2.1) hsame
      simp only [Prod.fst,Prod.snd] at he
      omega
  · intro x hx heq
    by_cases hj : j=0
    · subst j
      have hle := hiddenC_lift_lower_bound P.M.base R.e R.HD hd hx.1 heq
      have hlt := hc rfl
      omega
    · have hd' : HerzogLShapeDomain R.HD i (j-1) := by
        unfold HerzogLShapeDomain at *; omega
      have hxeq : normalizedGrid P.M.base R.e r i (j-1)=x := by
        have hmul := congrArg (fun t => t*routingC P.M.base R.e)
          (show j-1+1=j by omega)
        simp only [normalizedGrid,Nat.add_mul,one_mul] at heq hmul ⊢
        omega
      have hmem := (actual_chart_staircase_iff R hm hn r i (j-1) hd').mp
        (hxeq.symm ▸ hx)
      have hsame := hmin.2 (r,i,j-1) hmem (by rfl) (by rfl) (by dsimp; omega)
      have he := congrArg (fun z : Monomial => z.2.2) hsame
      simp only [Prod.fst,Prod.snd] at he
      omega

/-- Every canonical polynomial-minimal chart vector is literally one
of the frozen initial cut generators, not just equal in numerical degree. -/
theorem chartMinimal_on_domain_mem_generators (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {z : Monomial}
    (hd : HerzogLShapeDomain HD z.2.1 z.2.2) (hz : ChartMinimal B e HD z) :
    z ∈ canonicalIdealGenerators B e HD := by
  obtain ⟨g,hg,hr,hi,hj⟩ := (chart_on_domain_iff B e HD z hd).mp hz.1
  have hgm : g ∈ monomialClosure (chartGenerators B e HD) :=
    ⟨g,Or.inl hg,le_refl _,le_refl _,le_refl _⟩
  exact (hz.2 g hgm hr hi hj) ▸ hg

/-- All non-principal T3 generator families have strict hidden-wrap depth.
No G2/G3/source/count conclusion is assumed here. -/
theorem colonMonomials_hidden_bounds (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {i j d : ℕ} {z : Monomial}
    (hd : 0<d) (hcases : PreprincipalCases B e HD i j d)
    (hz : z ∈ colonMonomials B e HD i j d) :
    (z.2.1=0 → z.1 < if cr23 HD ≤ z.2.2 then cr21 HD else c1 B e) ∧
    (z.2.2=0 → z.1 < if cr32 HD ≤ z.2.1 then cr31 HD else c1 B e) := by
  have hs := coherent_coefficients B e HD
  have hp := coherent_coefficients_positive B e HD
  by_cases hi : i < cr12 HD
  · by_cases hj : j < cr13 HD
    · simp only [colonMonomials,hi,hj,ite_true,Set.mem_ofPred_eq] at hz
      rcases hz with rfl | rfl | rfl | rfl <;>
        simp only [Prod.fst,Prod.snd] <;>
        rcases hcases with h | h | h <;>
        constructor <;> intro h0 <;> split_ifs <;> omega
    · simp only [colonMonomials,hi,hj,ite_true,ite_false,Set.mem_ofPred_eq] at hz
      rcases hz with rfl | rfl | rfl <;>
        simp only [Prod.fst,Prod.snd] <;>
        rcases hcases with h | h | h <;>
        constructor <;> intro h0 <;> split_ifs <;> omega
  · simp only [colonMonomials,hi,ite_false,Set.mem_ofPred_eq] at hz
    rcases hz with rfl | rfl | rfl <;>
      simp only [Prod.fst,Prod.snd] <;>
      rcases hcases with h | h | h <;>
      constructor <;> intro h0 <;> split_ifs <;> omega

/-- The byte-exact R21 first-missing binder, now proved. PB is excluded
universally over genuine principal forms; PC is removed by frozen R21 G4.
Every other family has ordinary divisor exclusion and strict R14 wrap lift. -/
theorem actual_canonical_minimal_chart_source {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    ∀ r i j : ℕ, HerzogLShapeDomain R.HD i j →
    (r,i,j) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) →
    (∀ z ∈ monomialClosure (chartGenerators P.M.base R.e R.HD),
      z.1 ≤ r → z.2.1 ≤ i → z.2.2 ≤ j → z=(r,i,j)) →
    (∀ delta U V : ℕ, HerzogLShapeDomain R.HD U V →
      firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e)
        (routingM_pos P.M.base R.e) * routingM P.M.base R.e =
        normalizedGrid P.M.base R.e delta U V →
      (r,i,j) ≠ (delta+cr21 R.HD,0,V+cr23 R.HD)) →
    ∀ x h : ℕ,
      x ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      h ∈ routingH P.M.base R.e →
      normalizedGrid P.M.base R.e r i j=x+h → h=0 := by
  intro r i j hdom hmem hminimal hnotPB
  have hmin : ChartMinimal P.M.base R.e R.HD (r,i,j) := ⟨hmem,hminimal⟩
  have hg := chartMinimal_on_domain_mem_generators P.M.base R.e R.HD hdom hmin
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  rcases hg with heq | hcolon | hprincipal
  · simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl,rfl,rfl⟩
    apply chartMinimal_literal_of_wrap_bounds R hm hn _ _ _ hdom hmin
    · intro _; split_ifs <;> have hG0 := (normalized_mixed_notch_G0_G4 R hm hn).1 <;> omega
    · intro _; split_ifs <;> have hG0 := (normalized_mixed_notch_G0_G4 R hm hn).1 <;> omega
  · obtain ⟨n,u,v,d,_,_,hd,_,hcases,hz⟩ := hcolon
    obtain ⟨hb,hc⟩ := colonMonomials_hidden_bounds P.M.base R.e R.HD hd hcases hz
    exact chartMinimal_literal_of_wrap_bounds R hm hn r i j hdom hmin hb hc
  · obtain ⟨delta,U,V,hd,hform,heq⟩ := hprincipal
    rcases heq with heq | heq | heq
    · have hdg : normalizedGrid P.M.base R.e r i j =
          firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e)
            (routingM_pos P.M.base R.e) * routingM P.M.base R.e := by
        change monomialDegree P.M.base R.e (r,i,j)=_
        rw [heq]
        exact hform.symm
      rw [hdg]
      exact ((minimalTail_iff_literal _ _ _).mp
        (firstPrincipal_minimal_cut_source _ _ (routingM_pos P.M.base R.e))).2
    · exact False.elim (hnotPB delta U V hd hform heq)
    · rw [heq] at hmin
      obtain ⟨z,hz,hr,hi,hj,hne⟩ := actual_PC_proper_cut_divisor R hm hn delta U
      have hzm : z ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) := by
        obtain ⟨g,hg,hdiv⟩ := hz
        exact ⟨g,Or.inl hg,hdiv⟩
      exact False.elim (hne (hmin.2 z hzm hr hi (by dsimp; omega)))

theorem routingB_positive (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < routingB B e := by
  have hm := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  apply Nat.pos_of_ne_zero
  intro hz
  apply hm.2.2.1
  simpa only [routingB,hz] using (AddSubmonoid.zero_mem _)

theorem routingC_positive (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < routingC B e := by
  have hm := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  apply Nat.pos_of_ne_zero
  intro hz
  apply hm.2.2.2
  simpa only [routingC,hz] using (AddSubmonoid.zero_mem _)

/-- Source-to-chart direction: a proper coordinate divisor gives a
NONZERO actual H summand. L-shape downward closure is proved, not assumed. -/
theorem actual_H_source_canonical_chart_minimal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hd : HerzogLShapeDomain R.HD i j)
    (hsource : IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid
      (cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
      (normalizedGrid P.M.base R.e r i j)) :
    ChartMinimal P.M.base R.e R.HD (r,i,j) := by
  obtain ⟨hcut,hminimal⟩ := (minimalTail_iff_literal _ _ _).mp hsource
  refine ⟨(actual_chart_staircase_iff R hm hn r i j hd).mp hcut,?_⟩
  intro z hz hr hi hj
  simp only [Prod.fst,Prod.snd] at hr hi hj
  have hd' : HerzogLShapeDomain R.HD z.2.1 z.2.2 := by
    unfold HerzogLShapeDomain at *; omega
  have hzcut := (actual_chart_staircase_iff R hm hn z.1 z.2.1 z.2.2 hd').mpr hz
  have heq : normalizedGrid P.M.base R.e r i j =
      normalizedGrid P.M.base R.e z.1 z.2.1 z.2.2 +
      normalizedGrid P.M.base R.e (r-z.1) (i-z.2.1) (j-z.2.2) := by
    have ha := congrArg (fun t => t*routingA P.M.base R.e) (Nat.sub_add_cancel hr)
    have hb := congrArg (fun t => t*routingB P.M.base R.e) (Nat.sub_add_cancel hi)
    have hc := congrArg (fun t => t*routingC P.M.base R.e) (Nat.sub_add_cancel hj)
    simp only [Nat.add_mul,normalizedGrid] at *
    omega
  have hzero := hminimal _ _ hzcut (grid_mem P.M.base R.e _ _ _) heq
  have hap := routingA_pos P.M.base R.e
  have hbp := routingB_positive P.M.base R.e
  have hcp := routingC_positive P.M.base R.e
  simp only [normalizedGrid] at hzero
  have hre : z.1=r := by
    have hp : (r-z.1)*routingA P.M.base R.e=0 := by omega
    have ht := (Nat.mul_eq_zero.mp hp).resolve_right (Nat.ne_of_gt hap)
    omega
  have hie : z.2.1=i := by
    have hp : (i-z.2.1)*routingB P.M.base R.e=0 := by omega
    have ht := (Nat.mul_eq_zero.mp hp).resolve_right (Nat.ne_of_gt hbp)
    omega
  have hje : z.2.2=j := by
    have hp : (j-z.2.2)*routingC P.M.base R.e=0 := by omega
    have ht := (Nat.mul_eq_zero.mp hp).resolve_right (Nat.ne_of_gt hcp)
    omega
  exact Prod.ext hre (Prod.ext hie hje)

/-- Literal PB numerical relation: its principal source has a positive
b-tail because the principal form has U<I. -/
theorem PB_degree_eq_principal_plus_b (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {delta U V : ℕ}
    (hd : HerzogLShapeDomain HD U V)
    (hform : firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) *
      routingM B e=normalizedGrid B e delta U V) :
    monomialDegree B e (delta+cr21 HD,0,V+cr23 HD) =
      firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)*routingM B e +
        (c2 B e-U)*routingB B e := by
  have hr := (coherent_normalized_relations B e HD).2.1
  have hI := congrArg (fun t => t*routingB B e)
    (Nat.sub_add_cancel (Nat.le_of_lt hd.1))
  simp only [monomialDegree,normalizedGrid,Nat.add_mul,zero_mul,zero_add,add_zero] at *
  omega

/-- PB is NEVER an H-source, even in the legal case where it is a
polynomial-minimal generator. Exhibits an actual literal cut predecessor. -/
theorem PB_has_actual_cut_predecessor (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {delta U V : ℕ}
    (hd : HerzogLShapeDomain HD U V)
    (hform : firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) *
      routingM B e=normalizedGrid B e delta U V) :
    ∃ x ∈ cyclicCut (routingH B e) (routingM B e),
      monomialDegree B e (delta+cr21 HD,0,V+cr23 HD)=x+routingB B e := by
  let q0 := firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)
  have hp := firstPrincipal_spec (routingH B e) (routingM B e) (routingM_pos B e)
  have hcut : q0*routingM B e ∈ cyclicCut (routingH B e) (routingM B e) :=
    ⟨hp.2,q0,hp.1,0,(routingH B e).toAddSubmonoid.zero_mem,by simp⟩
  refine ⟨q0*routingM B e + normalizedGrid B e 0 (c2 B e-U-1) 0,
    cut_add hcut (grid_mem B e _ _ _),?_⟩
  rw [PB_degree_eq_principal_plus_b B e HD hd hform]
  have hU := hd.1
  have hI := congrArg (fun t => t*routingB B e)
    (show c2 B e-U-1+1=c2 B e-U by omega)
  simp only [normalizedGrid,Nat.add_mul,zero_mul,zero_add,add_zero,one_mul] at *
  dsimp [q0]
  omega

theorem PB_not_H_source (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {delta U V : ℕ}
    (hd : HerzogLShapeDomain HD U V)
    (hform : firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) *
      routingM B e=normalizedGrid B e delta U V) :
    ¬ IsMinimalTailGenerator (routingH B e).toAddSubmonoid
      (cyclicCut (routingH B e) (routingM B e))
      (monomialDegree B e (delta+cr21 HD,0,V+cr23 HD)) := by
  intro hs
  obtain ⟨x,hx,heq⟩ := PB_has_actual_cut_predecessor B e HD hd hform
  have hzero := ((minimalTail_iff_literal _ _ _).mp hs).2 x _ hx (routingHB B e) heq
  exact (Nat.ne_of_gt (routingB_positive B e)) hzero

/-- The full source dictionary at canonical coordinates, including the
universal genuine-principal PB exception, in both directions. -/
theorem actual_canonical_chart_source_iff {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hd : HerzogLShapeDomain R.HD i j) :
    IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid
      (cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
      (normalizedGrid P.M.base R.e r i j) ↔
    ChartMinimal P.M.base R.e R.HD (r,i,j) ∧
      ∀ delta U V, HerzogLShapeDomain R.HD U V →
        firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e)
          (routingM_pos P.M.base R.e)*routingM P.M.base R.e =
            normalizedGrid P.M.base R.e delta U V →
        (r,i,j) ≠ (delta+cr21 R.HD,0,V+cr23 R.HD) := by
  constructor
  · intro hs
    refine ⟨actual_H_source_canonical_chart_minimal R hm hn r i j hd hs,?_⟩
    intro delta U V hd' hf heq
    apply PB_not_H_source P.M.base R.e R.HD hd' hf
    change IsMinimalTailGenerator _ _ (monomialDegree P.M.base R.e (r,i,j)) at hs
    simpa only [heq] using hs
  · rintro ⟨hmin,hPB⟩
    apply (minimalTail_iff_literal _ _ _).mpr
    exact ⟨(actual_chart_staircase_iff R hm hn r i j hd).mpr hmin.1,
      actual_canonical_minimal_chart_source R hm hn r i j hd hmin.1 hmin.2 hPB⟩

/-- Actual G2 forces y^I to be polynomial-minimal; no H-source is
assigned to this noncanonical chart vector. -/
theorem actual_pureB_chart_minimal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    ChartMinimal P.M.base R.e R.HD (0,c2 P.M.base R.e,0) := by
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hG2 := (normalized_mixed_notch_G0_G4 R hm hn).2.2.1
  refine ⟨⟨(0,c2 P.M.base R.e,0),Or.inr (Or.inl rfl),le_refl _,le_refl _,le_refl _⟩,?_⟩
  rintro ⟨r,i,j⟩ hz hr hi hj
  simp only [Prod.fst,Prod.snd] at hr hi hj
  have hr0 : r=0 := by omega
  have hj0 : j=0 := by omega
  subst r; subst j
  by_cases he : i=c2 P.M.base R.e
  · simp [he]
  · have hi' : i ≤ c2 P.M.base R.e-1 := by omega
    have hd : HerzogLShapeDomain R.HD (c2 P.M.base R.e-1) 0 := by
      unfold HerzogLShapeDomain; omega
    have hc := (actual_chart_staircase_iff R hm hn 0 _ 0 hd).mpr
      (monomialClosure_upward hz (by rfl) hi' (by rfl))
    have hiI := (actual_cyclicCut_iff_routingI P.M.base R.e _).mp hc
    have hzero := (normalizedGrid_mem_iff_eta_le P.M.base R.e 0 _ 0).mp hiI
    omega

theorem actual_pureC_chart_minimal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    ChartMinimal P.M.base R.e R.HD (0,0,c3 P.M.base R.e) := by
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hG3 := (normalized_mixed_notch_G0_G4 R hm hn).2.2.2.1
  refine ⟨⟨(0,0,c3 P.M.base R.e),Or.inr (Or.inr (Or.inl rfl)),le_refl _,le_refl _,le_refl _⟩,?_⟩
  rintro ⟨r,i,j⟩ hz hr hi hj
  simp only [Prod.fst,Prod.snd] at hr hi hj
  have hr0 : r=0 := by omega
  have hi0 : i=0 := by omega
  subst r; subst i
  by_cases he : j=c3 P.M.base R.e
  · simp [he]
  · have hj' : j ≤ c3 P.M.base R.e-1 := by omega
    have hd : HerzogLShapeDomain R.HD 0 (c3 P.M.base R.e-1) := by
      unfold HerzogLShapeDomain; omega
    have hc := (actual_chart_staircase_iff R hm hn 0 0 _ hd).mpr
      (monomialClosure_upward hz (by rfl) (by rfl) hj')
    have hiI := (actual_cyclicCut_iff_routingI P.M.base R.e _).mp hc
    have hzero := (normalizedGrid_mem_iff_eta_le P.M.base R.e 0 0 _).mp hiI
    omega

/-- These are genuinely off-domain, so they cannot be silently put into
the canonical source-coordinate type or its bijection. -/
theorem pure_chart_vectors_not_canonical (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) :
    ¬ HerzogLShapeDomain HD (c2 B e) 0 ∧ ¬ HerzogLShapeDomain HD 0 (c3 B e) := by
  unfold HerzogLShapeDomain
  omega

theorem actual_central_chart_not_minimal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    ¬ ChartMinimal P.M.base R.e R.HD (0,cr12 R.HD,cr13 R.HD) := by
  intro hmin
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hg := (normalized_mixed_notch_G0_G4 R hm hn).2.1
  have hd : HerzogLShapeDomain R.HD (cr12 R.HD) (cr13 R.HD-1) := by
    unfold HerzogLShapeDomain; omega
  have hI := (normalizedGrid_mem_iff_eta_le P.M.base R.e 0 _ _).mpr (by rw [hg])
  have hK := (actual_cyclicCut_iff_routingI P.M.base R.e _).mpr hI
  have hmemb := (actual_chart_staircase_iff R hm hn 0 _ _ hd).mp hK
  have heq := hmin.2 (0,cr12 R.HD,cr13 R.HD-1) hmemb
    (by rfl) (by rfl) (by dsimp; omega)
  have hje := congrArg (fun z : Monomial => z.2.2) heq
  simp only [Prod.fst,Prod.snd] at hje
  omega

theorem actual_PC_not_chart_minimal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) (delta U : ℕ) :
    ¬ ChartMinimal P.M.base R.e R.HD (delta+cr31 R.HD,U+cr32 R.HD,0) := by
  intro hmin
  obtain ⟨z,hz,hr,hi,hj,hne⟩ := actual_PC_proper_cut_divisor R hm hn delta U
  have hzm : z ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) := by
    obtain ⟨g,hg,hdiv⟩ := hz
    exact ⟨g,Or.inl hg,hdiv⟩
  exact hne (hmin.2 z hzm hr hi (by dsimp; omega))

/-- Every actual H element has one canonical monomial, derived from
frozen terminating Herzog reduction; numerical equality is used only
after domain proofs for both coordinates. -/
theorem canonical_monomial_of_H (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {x : ℕ}
    (hx : x ∈ routingH B e) :
    ∃! z : Monomial, HerzogLShapeDomain HD z.2.1 z.2.2 ∧ monomialDegree B e z=x := by
  obtain ⟨r,i,j,hfac⟩ := routingH_factorization B e hx
  obtain ⟨z,_hpath,hdom,hdegree⟩ := rewrite_normalizes B e HD (r,i,j)
  have hzx : monomialDegree B e z=x := by
    rw [←hdegree]
    exact hfac.symm
  refine ⟨z,⟨hdom,hzx⟩,?_⟩
  intro z' hz'
  exact canonical_monomial_unique B e HD hz'.1 hdom (hz'.2.trans hzx.symm)

end NS25Lean.L5A2C4OR22
