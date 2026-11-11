import NS25Lean.SharedTailPositiveChart

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse L3C

theorem Positive.normal_form_unique {H : NumericalSemigroup} (D : Positive H)
    (s i j s' i' j' : ℕ) (hc : D.ChartA i j) (hc' : D.ChartA i' j')
    (he : s*D.a+i*D.b+j*D.c=s'*D.a+i'*D.b+j'*D.c) :
    s=s' ∧ i=i' ∧ j=j' := by
  suffices hm : ∀ (s i j s' i' j' : ℕ), D.ChartA i j → D.ChartA i' j' →
      s≤s' → s*D.a+i*D.b+j*D.c=s'*D.a+i'*D.b+j'*D.c →
      s=s' ∧ i=i' ∧ j=j' by
    rcases le_total s s' with hs | hs
    · exact hm s i j s' i' j' hc hc' hs he
    · obtain ⟨h0,h1,h2⟩ := hm s' i' j' s i j hc' hc hs he.symm
      exact ⟨h0.symm,h1.symm,h2.symm⟩
  intro s i j s' i' j' hc hc' hss he
  have hsub := Nat.sub_add_cancel hss
  have hw : D.triple.weight (vector (s'-s) i' j')=i*D.b+j*D.c := by
    rw [vector_weight,Triple.grid]
    change (s'-s)*D.a+i'*D.b+j'*D.c=i*D.b+j*D.c
    nlinarith
  have hu := D.chartA_factorization_unique i j hc _ hw
  have h0 := congrArg (fun v : Exponent => v 0) hu
  have h1 := congrArg (fun v : Exponent => v 1) hu
  have h2 := congrArg (fun v : Exponent => v 2) hu
  simp only [vector_zero,vector_one,vector_two] at h0 h1 h2
  exact ⟨by omega,h1.symm,h2.symm⟩

/-- The actual Apéry set equals the displayed canonical omitted-axis chart. -/
theorem Positive.apery_chart_iff {H : NumericalSemigroup} (D : Positive H) (h : ℕ) :
    h∈FourGeneratedBridge.aperySet H.toAddSubmonoid D.a ↔
      ∃ i j : ℕ, D.ChartA i j ∧ h=i*D.b+j*D.c := by
  constructor
  · intro hh
    obtain ⟨s,i,j,hc,he⟩ := D.normal_form_exists h hh.1
    have hs : s=0 := by
      by_contra hn
      have hp : 0<s := Nat.pos_of_ne_zero hn
      have hm : (s-1)*D.a+i*D.b+j*D.c∈H := by
        simpa [vector_weight,Triple.grid] using D.triple.member (vector (s-1) i j)
      have hsub := Nat.sub_add_cancel hp
      have hmul := congrArg (fun n => n*D.a) hsub
      simp only [Nat.add_mul,Nat.one_mul] at hmul
      norm_num at hmul
      have hsa : D.a≤h := by omega
      have hcancel := Nat.sub_add_cancel hsa
      have heq : h-D.a=(s-1)*D.a+i*D.b+j*D.c := by omega
      rcases hh.2 with hlt | hnot
      · have ha := D.triple.positive 0
        change 0<D.a at ha
        nlinarith
      · exact hnot (heq.symm ▸ hm)
    exact ⟨i,j,hc,by simpa [hs] using he⟩
  · rintro ⟨i,j,hc,rfl⟩
    exact D.chartA_apery i j hc

theorem Positive.arbitrary_pair_unique {H : NumericalSemigroup} (D : Positive H)
    (i j i' j' : ℕ) (hc : D.ChartA i j)
    (he : i*D.b+j*D.c=i'*D.b+j'*D.c) : i'=i ∧ j'=j := by
  have hu := D.chartA_factorization_unique i j hc (vector 0 i' j')
    (by simpa [vector_weight,Triple.grid] using he.symm)
  have h1 := congrArg (fun v : Exponent => v 1) hu
  have h2 := congrArg (fun v : Exponent => v 2) hu
  exact ⟨by simpa using h1,by simpa using h2⟩

/-- The finite critical moves really generate the full polynomial kernel;
this is independent of the auxiliary cut/pivot chosen to expose Mode. -/
theorem Positive.exact_ideal {H : NumericalSemigroup} (D : Positive H)
    (k : Type*) [Field k] :
    Presentation.relationIdeal k (D.toMode 1 (by decide)).relations=
      Presentation.relationIdeal k {lr : Exponent×Exponent |
        D.triple.weight lr.1=D.triple.weight lr.2} := by
  simpa only [Positive.toBase] using mode_exact_ideal (D.toMode 1 (by decide)) k

theorem Positive.connected {H : NumericalSemigroup} (D : Positive H)
    (e f : Exponent) (he : D.triple.weight e=D.triple.weight f) :
    ContextPath (D.toMode 1 (by decide)).relations e f :=
  mode_connected (D.toMode 1 (by decide)) e f he

end NS25Lean.SharedTail
