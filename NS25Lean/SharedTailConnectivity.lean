import NS25Lean.P2CriticalPresentationModes

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse CriticalCapGeometry CriticalPresentationModes L3C
abbrev Exponent := Fin 3 →₀ ℕ

theorem exponent_eq_vector (e : Exponent) : e=vector (e 0) (e 1) (e 2) := by
  ext i
  fin_cases i <;> simp

def Pure (e : Exponent) : Prop := ∃ (i : Fin 3) (n : ℕ), 0<n ∧ e=Finsupp.single i n

theorem disjoint_one_pure (e f : Exponent) (he : e≠0) (hf : f≠0)
    (hdis : ∀ i : Fin 3, e i=0 ∨ f i=0) : Pure e ∨ Pure f := by
  classical
  have hd : Disjoint e.support f.support := by
    apply Finset.disjoint_left.mpr
    intro i hei hfi
    have he' := Finsupp.mem_support_iff.mp hei
    have hf' := Finsupp.mem_support_iff.mp hfi
    rcases hdis i with h | h
    · exact he' h
    · exact hf' h
  have hcard : e.support.card+f.support.card≤3 := by
    rw [←Finset.card_union_of_disjoint hd]
    simpa using Finset.card_le_card (Finset.subset_univ (e.support∪f.support))
  have p (u : Exponent) (hu : u≠0) (hc : u.support.card≤1) : Pure u := by
    obtain ⟨i,hi⟩ : ∃ i : Fin 3, u i≠0 := by
      by_contra hn
      push Not at hn
      exact hu (by ext i; exact hn i)
    have hm : i∈u.support := Finsupp.mem_support_iff.mpr hi
    have hcp := Finset.card_pos.mpr ⟨i,hm⟩
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (show u.support.card=1 by omega)
    have hij : i=j := by simpa [hj] using hm
    subst j
    refine ⟨i,u i,Nat.pos_of_ne_zero hi,?_⟩
    ext k
    by_cases hk : k=i
    · subst k; simp
    · have hn : k∉u.support := by simp [hj,hk]
      have hz : u k=0 := by
        by_contra h
        exact hn (Finsupp.mem_support_iff.mpr h)
      simp [hk,hz]
  by_cases hc : e.support.card≤1
  · exact Or.inl (p e he hc)
  · exact Or.inr (p f hf (by omega))

theorem context_step_of_relation (S : Set (Exponent×Exponent))
    (l r d : Exponent) (hlr : (l,r)∈S) : ContextPath S (l+d) (r+d) :=
  .single ⟨(l,r),hlr,d,Or.inl ⟨by rw [add_comm],by rw [add_comm]⟩⟩

theorem contextPath_generated (S : Set (Exponent×Exponent)) {e f : Exponent}
    (hp : ContextPath S e f) : Presentation.generatedCongruence S e f := by
  induction hp with
  | refl => exact .refl _
  | @tail v w _ hvw ih =>
    obtain ⟨⟨l,r⟩,hlr,d,h⟩ := hvw
    have hl : Presentation.generatedCongruence S l r := AddConGen.Rel.of l r hlr
    have hd : Presentation.generatedCongruence S d d := .refl _
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ih.trans (hd.add hl)
    · exact ih.trans (hd.add hl.symm)

theorem shared_coordinate_path {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent)) (h : ℕ)
    (ih : ∀ n<h, ∀ e f : Exponent, T.weight e=n → T.weight f=n → ContextPath S e f)
    (e f : Exponent) (he : T.weight e=h) (hf : T.weight f=h)
    (j : Fin 3) (hej : 0<e j) (hfj : 0<f j) : ContextPath S e f := by
  have headd : Finsupp.single j 1+(e-Finsupp.single j 1)=e :=
    add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hej)
  have hfadd : Finsupp.single j 1+(f-Finsupp.single j 1)=f :=
    add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hfj)
  have hew := congrArg T.weight headd
  have hfw := congrArg T.weight hfadd
  simp only [map_add,T.weight_single,one_mul,he,hf] at hew hfw
  have hp := T.positive j
  change 0<T.g j at hp
  have hsmall : h-T.g j<h := by omega
  have hpath := ih (h-T.g j) hsmall (e-Finsupp.single j 1) (f-Finsupp.single j 1)
    (by omega) (by omega)
  simpa only [headd,hfadd] using contextPath_add S hpath (Finsupp.single j 1)

/-- Whole-fiber induction: a proved bridge between disjoint vertices is enough.
The bridge is a local move construction, not an ideal-generation assumption. -/
theorem connected_of_disjoint_bridges {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (bridge : ∀ e f : Exponent, e≠0 → f≠0 → T.weight e=T.weight f →
      (∀ i, e i=0 ∨ f i=0) → ∃ u v : Exponent,
      ContextPath S e u ∧ ContextPath S f v ∧
      T.weight u=T.weight e ∧ T.weight v=T.weight f ∧
      ∃ j, 0<u j ∧ 0<v j) :
    ∀ e f : Exponent, T.weight e=T.weight f → ContextPath S e f := by
  suffices h : ∀ n, ∀ e f : Exponent, T.weight e=n → T.weight f=n → ContextPath S e f by
    intro e f he
    exact h (T.weight e) e f rfl he.symm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro e f he hf
    by_cases hef : e=f
    · subst f; exact .refl
    have hen : e≠0 := by
      intro hz
      have hfw : T.weight f=0 := by rw [hf,←he,hz,map_zero]
      exact hef (hz.trans (T.weight_eq_zero hfw).symm)
    have hfn : f≠0 := by
      intro hz
      have hew : T.weight e=0 := by rw [he,←hf,hz,map_zero]
      exact hef ((T.weight_eq_zero hew).trans hz.symm)
    by_cases hs : ∃ j, 0<e j ∧ 0<f j
    · obtain ⟨j,hej,hfj⟩ := hs
      exact shared_coordinate_path T S n ih e f he hf j hej hfj
    · have hdis : ∀ i, e i=0 ∨ f i=0 := by
        intro i
        by_cases hi : e i=0
        · exact Or.inl hi
        · right
          by_contra hj
          exact hs ⟨i,Nat.pos_of_ne_zero hi,Nat.pos_of_ne_zero hj⟩
      obtain ⟨u,v,heu,hfv,huw,hvw,j,huj,hvj⟩ := bridge e f hen hfn (he.trans hf.symm) hdis
      exact heu.trans ((shared_coordinate_path T S n ih u v
        (huw.trans he) (hvw.trans hf) j huj hvj).trans (contextPath_symm S hfv))

theorem ideal_eq_of_connected {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent)) (hrel : ∀ p∈S, T.weight p.1=T.weight p.2)
    (hconnect : ∀ e f : Exponent, T.weight e=T.weight f → ContextPath S e f)
    (k : Type*) [Field k] : Presentation.relationIdeal k S=
      Presentation.relationIdeal k {p : Exponent×Exponent | T.weight p.1=T.weight p.2} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact Ideal.subset_span ⟨p,hrel p hp,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨e,f⟩,hef,rfl⟩
    exact Presentation.relationBinomial_mem_of_generated k S e f
      (contextPath_generated S (hconnect e f hef))

end NS25Lean.SharedTail
