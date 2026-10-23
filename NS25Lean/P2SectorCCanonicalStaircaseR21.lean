import NS25Lean.P2SectorCColonExactR20

set_option linter.style.header false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NS25Lean.L5A2C4OR21
open L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR3
  L5A2C4OR4 L5A2C4OR5 L5A2C4OR6 L5A2C4OR19 L5A2C4OR20
variable {Gamma : NumericalSemigroup}

/-- Literal exponent rewrites, with central then b then c priority. -/
inductive HerzogRewrite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Monomial → Monomial → Prop
  | central (r i j : ℕ) (hp : cr12 HD ≤ i) (hq : cr13 HD ≤ j) :
      HerzogRewrite B e HD (r,i,j) (r+c1 B e,i-cr12 HD,j-cr13 HD)
  | bWrap (r i j : ℕ) (hc : ¬(cr12 HD ≤ i ∧ cr13 HD ≤ j))
      (hi : c2 B e ≤ i) :
      HerzogRewrite B e HD (r,i,j) (r+cr21 HD,i-c2 B e,j+cr23 HD)
  | cWrap (r i j : ℕ) (hc : ¬(cr12 HD ≤ i ∧ cr13 HD ≤ j))
      (hi : ¬c2 B e ≤ i) (hj : c3 B e ≤ j) :
      HerzogRewrite B e HD (r,i,j) (r+cr31 HD,i+cr32 HD,j-c3 B e)

def transverse (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (z : Monomial) : ℕ := z.2.1 * routingB B e + z.2.2 * routingC B e

theorem rewrite_arithmetic (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z z' : Monomial}
    (h : HerzogRewrite B e HD z z') :
    monomialDegree B e z = monomialDegree B e z' ∧
      z.1 < z'.1 ∧ transverse B e z' < transverse B e z := by
  have hr := coherent_normalized_relations B e HD
  have hp := coherent_coefficients_positive B e HD
  have ha := routingA_pos B e
  have hC : 0 < c1 B e := by
    have hs := coherent_coefficients B e HD
    omega
  cases h with
  | central r i j hi hj =>
    have hb := congrArg (fun n => n * routingB B e) (Nat.sub_add_cancel hi)
    have hc := congrArg (fun n => n * routingC B e) (Nat.sub_add_cancel hj)
    simp only [Nat.add_mul] at hb hc
    simp only [monomialDegree, normalizedGrid, transverse, Prod.fst, Prod.snd,
      Nat.add_mul]
    constructor
    · nlinarith only [hr.1, hb, hc]
    constructor
    · omega
    · nlinarith [hr.1]
  | bWrap r i j _ hi =>
    have hb := congrArg (fun n => n * routingB B e) (Nat.sub_add_cancel hi)
    simp only [Nat.add_mul] at hb
    simp only [monomialDegree, normalizedGrid, transverse, Prod.fst, Prod.snd,
      Nat.add_mul]
    constructor
    · nlinarith only [hr.2.1, hb]
    constructor
    · omega
    · nlinarith [hr.2.1]
  | cWrap r i j _ _ hj =>
    have hc := congrArg (fun n => n * routingC B e) (Nat.sub_add_cancel hj)
    simp only [Nat.add_mul] at hc
    simp only [monomialDegree, normalizedGrid, transverse, Prod.fst, Prod.snd,
      Nat.add_mul]
    constructor
    · nlinarith only [hr.2.2, hc]
    constructor
    · omega
    · nlinarith [hr.2.2]

theorem rewrite_terminal_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    (¬∃ z', HerzogRewrite B e HD z z') ↔ HerzogLShapeDomain HD z.2.1 z.2.2 := by
  obtain ⟨r,i,j⟩ := z
  constructor
  · intro ht
    have hc : ¬(cr12 HD ≤ i ∧ cr13 HD ≤ j) := by
      intro h
      exact ht ⟨_, HerzogRewrite.central r i j h.1 h.2⟩
    have hb : ¬c2 B e ≤ i := by
      intro h
      exact ht ⟨_, HerzogRewrite.bWrap r i j hc h⟩
    have hw : ¬c3 B e ≤ j := by
      intro h
      exact ht ⟨_, HerzogRewrite.cWrap r i j hc hb h⟩
    change HerzogLShapeDomain HD i j
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hi,hj,hcorner⟩ ⟨z',h⟩
    cases h <;> simp only [Prod.fst, Prod.snd] at * <;> omega

/-- Totality on every noncanonical natural exponent vector. -/
theorem rewrite_exists_of_not_domain (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) (z : Monomial)
    (hz : ¬HerzogLShapeDomain HD z.2.1 z.2.2) :
    ∃ z', HerzogRewrite B e HD z z' := by
  by_contra h
  exact hz ((rewrite_terminal_iff B e HD z).mp h)

private theorem closure_of_height (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {z : Monomial}
    (h : H0 B e ≤ z.1) : z ∈ monomialClosure (canonicalIdealGenerators B e HD) :=
  ⟨(H0 B e,0,0), Or.inl rfl, h, Nat.zero_le _, Nat.zero_le _⟩

/-- The complete T3 divisor calculation on ARBITRARY multiples. Central is
absorbed by x^H0; wrap cases exhibit a listed alternate or retain a divisor.
No equality of numerical degrees is used to infer ideal membership. -/
private theorem colon_wrap_preservation (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {i j d : ℕ}
    (h0 : H0 B e < c1 B e) (hcases : PreprincipalCases B e HD i j d)
    {z z' : Monomial} (hstep : HerzogRewrite B e HD z z')
    (hz : z ∈ monomialClosure (colonMonomials B e HD i j d)) :
    H0 B e ≤ z'.1 ∨ z' ∈ monomialClosure (colonMonomials B e HD i j d) := by
  have hs := coherent_coefficients B e HD
  cases hstep with
  | central r u v hp hq => exact Or.inl (by simp only [Prod.fst]; omega)
  | bWrap r u v hc hu =>
    rcases hcases with hi | ht | hr
    · simp [monomialClosure, colonMonomials, hi.2.1, hi.2.2.2.1,
        or_and_right, exists_or] at hz ⊢
      omega
    · simp [monomialClosure, colonMonomials, ht.2.1,
        Nat.not_lt.mpr ht.2.2.1, or_and_right, exists_or] at hz ⊢
      omega
    · simp [monomialClosure, colonMonomials, Nat.not_lt.mpr hr.1,
        or_and_right, exists_or] at hz ⊢
      omega
  | cWrap r u v hc hu hv =>
    rcases hcases with hi | ht | hr
    · simp [monomialClosure, colonMonomials, hi.2.1, hi.2.2.2.1,
        or_and_right, exists_or] at hz ⊢
      omega
    · simp [monomialClosure, colonMonomials, ht.2.1,
        Nat.not_lt.mpr ht.2.2.1, or_and_right, exists_or] at hz ⊢
      omega
    · simp [monomialClosure, colonMonomials, Nat.not_lt.mpr hr.1,
        or_and_right, exists_or] at hz ⊢
      omega

private def principalTriples (HD : CoherentHerzogData B e)
    (delta U V : ℕ) : Set Monomial :=
  {z | z=(delta,U,V) ∨ z=(delta+cr21 HD,0,V+cr23 HD) ∨
    z=(delta+cr31 HD,U+cr32 HD,0)}

private theorem principal_preservation (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    (delta U V : ℕ) (h0 : H0 B e < c1 B e)
    {z z' : Monomial} (hstep : HerzogRewrite B e HD z z')
    (hz : z ∈ monomialClosure (principalTriples HD delta U V)) :
    H0 B e ≤ z'.1 ∨ z' ∈ monomialClosure (principalTriples HD delta U V) := by
  have hs := coherent_coefficients B e HD
  cases hstep <;>
    simp [monomialClosure, principalTriples, or_and_right, exists_or] at hz ⊢ <;>
    omega

theorem monomialClosure_rewrite_preserved (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    (h0 : H0 B e < c1 B e) {z z' : Monomial}
    (hstep : HerzogRewrite B e HD z z')
    (hz : z ∈ monomialClosure (canonicalIdealGenerators B e HD)) :
    z' ∈ monomialClosure (canonicalIdealGenerators B e HD) := by
  obtain ⟨g,hg,hdiv⟩ := hz
  rcases hg with rfl | hcolon | hprincipal
  · exact closure_of_height B e HD (le_trans hdiv.1 (Nat.le_of_lt
      (rewrite_arithmetic B e HD hstep).2.1))
  · obtain ⟨n,i,j,d,hn,hpre,hd,heq,hcases,hg⟩ := hcolon
    rcases colon_wrap_preservation B e HD h0 hcases hstep ⟨g,hg,hdiv⟩ with h | h
    · exact closure_of_height B e HD h
    · obtain ⟨g',hg',hdiv'⟩ := h
      exact ⟨g', Or.inr (Or.inl ⟨n,i,j,d,hn,hpre,hd,heq,hcases,hg'⟩), hdiv'⟩
  · obtain ⟨delta,U,V,hdom,heq,hg⟩ := hprincipal
    rcases principal_preservation B e HD delta U V h0 hstep ⟨g,hg,hdiv⟩ with h | h
    · exact closure_of_height B e HD h
    · obtain ⟨g',hg',hdiv'⟩ := h
      exact ⟨g', Or.inr (Or.inr ⟨delta,U,V,hdom,heq,hg'⟩), hdiv'⟩

/-- Finite legal iteration preserves the literal polynomial ideal. -/
theorem monomialClosure_rewrites_preserved (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    (h0 : H0 B e < c1 B e) {z z' : Monomial}
    (hpath : Relation.ReflTransGen (HerzogRewrite B e HD) z z')
    (hz : z ∈ monomialClosure (canonicalIdealGenerators B e HD)) :
    z' ∈ monomialClosure (canonicalIdealGenerators B e HD) := by
  induction hpath with
  | refl => exact hz
  | tail _ hstep ih => exact monomialClosure_rewrite_preserved B e HD h0 hstep ih

/-- Termination is witnessed by strict decrease of transverse degree, not
by a finite search or a presumed no-reentry statement. -/
theorem rewrite_normalizes (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) (z : Monomial) :
    ∃ z' : Monomial, Relation.ReflTransGen (HerzogRewrite B e HD) z z' ∧
      HerzogLShapeDomain HD z'.2.1 z'.2.2 ∧
      monomialDegree B e z = monomialDegree B e z' := by
  have go : ∀ n : ℕ, ∀ z : Monomial, transverse B e z = n →
      ∃ z' : Monomial, Relation.ReflTransGen (HerzogRewrite B e HD) z z' ∧
        HerzogLShapeDomain HD z'.2.1 z'.2.2 ∧
        monomialDegree B e z = monomialDegree B e z' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hn
      by_cases hd : HerzogLShapeDomain HD z.2.1 z.2.2
      · exact ⟨z, Relation.ReflTransGen.refl, hd, rfl⟩
      · obtain ⟨next,hstep⟩ := rewrite_exists_of_not_domain B e HD z hd
        have ha := rewrite_arithmetic B e HD hstep
        obtain ⟨last,hpath,hdom,hdegree⟩ :=
          ih (transverse B e next) (by omega) next rfl
        exact ⟨last, Relation.ReflTransGen.head hstep hpath, hdom,
          ha.1.trans hdegree⟩
  exact go _ z rfl

/-- Canonical uniqueness is only asserted with BOTH actual L-domain
proofs. The arbitrary input to normalization is never marked canonical. -/
theorem canonical_monomial_unique (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {z z' : Monomial}
    (hd : HerzogLShapeDomain HD z.2.1 z.2.2)
    (hd' : HerzogLShapeDomain HD z'.2.1 z'.2.2)
    (heq : monomialDegree B e z = monomialDegree B e z') : z = z' := by
  obtain ⟨r,i,j⟩ := z
  obtain ⟨r',i',j'⟩ := z'
  change HerzogLShapeDomain HD i j at hd
  change HerzogLShapeDomain HD i' j' at hd'
  change normalizedGrid B e r i j = normalizedGrid B e r' i' j' at heq
  obtain ⟨ij,_hij,hunique⟩ := coherent_lShape_unique_coordinate B e HD
    (normalizedGrid B e r i j)
  have hm : Int.ModEq (routingA B e)
      ((i : ℤ)*routingB B e+(j : ℤ)*routingC B e) (normalizedGrid B e r i j) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(r : ℤ), ?_⟩
    simp [normalizedGrid]
    ring
  have hm' : Int.ModEq (routingA B e)
      ((i' : ℤ)*routingB B e+(j' : ℤ)*routingC B e) (normalizedGrid B e r i j) := by
    rw [heq, Int.modEq_iff_dvd]
    refine ⟨(r' : ℤ), ?_⟩
    simp [normalizedGrid]
    ring
  have hpair : ((i : ℤ),(j : ℤ)) = ((i' : ℤ),(j' : ℤ)) :=
    (hunique _ ⟨inLShape_of_herzogDomain B e HD hd,hm⟩).trans
      (hunique _ ⟨inLShape_of_herzogDomain B e HD hd',hm'⟩).symm
  have hiZ : (i : ℤ)=i' := by simpa using congrArg Prod.fst hpair
  have hjZ : (j : ℤ)=j' := by simpa using congrArg Prod.snd hpair
  have hi : i=i' := by exact_mod_cast hiZ
  have hj : j=j' := by exact_mod_cast hjZ
  subst i'
  subst j'
  have ha := routingA_pos B e
  have hr : r=r' := by simp only [normalizedGrid] at heq; nlinarith
  subst r'
  rfl

/-- The missing inverse dictionary: each exact T3 degree has a literal
listed exponent vector. This is not a claim of canonicality. -/
theorem colon_degree_has_monomial (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) (i j d : ℕ)
    {g : ℕ} (hg : g ∈ preprincipalColonGenerators B e HD i j d) :
    ∃ z ∈ colonMonomials B e HD i j d, monomialDegree B e z = g := by
  by_cases hi : i < cr12 HD
  · by_cases hj : j < cr13 HD
    · simp only [preprincipalColonGenerators, hi,hj,ite_true] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ⟨(0,i,j),by simp [colonMonomials,hi,hj],rfl⟩
      · exact ⟨(cr31 HD-d,i+cr32 HD,0),by simp [colonMonomials,hi,hj],rfl⟩
      · exact ⟨(cr21 HD-d,0,j+cr23 HD),by simp [colonMonomials,hi,hj],rfl⟩
      · exact ⟨(c1 B e-d,0,0),by simp [colonMonomials,hi,hj],rfl⟩
    · simp only [preprincipalColonGenerators,hi,hj,ite_true,ite_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨(0,i,j),by simp [colonMonomials,hi,hj],rfl⟩
      · exact ⟨(cr31 HD-d,i+cr32 HD,0),by simp [colonMonomials,hi,hj],rfl⟩
      · exact ⟨(c1 B e-d,0,j-cr13 HD),by simp [colonMonomials,hi,hj],rfl⟩
  · simp only [preprincipalColonGenerators,hi,ite_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨(0,i,j),by simp [colonMonomials,hi],rfl⟩
    · exact ⟨(cr21 HD-d,0,j+cr23 HD),by simp [colonMonomials,hi],rfl⟩
    · exact ⟨(c1 B e-d,i-cr12 HD,0),by simp [colonMonomials,hi],rfl⟩

private theorem generator_multiple_representation (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) {g : Monomial}
    (hg : g ∈ canonicalIdealGenerators B e HD) {h : ℕ}
    (hh : h ∈ routingH B e) :
    ∃ z ∈ monomialClosure (canonicalIdealGenerators B e HD),
      monomialDegree B e z = monomialDegree B e g + h := by
  obtain ⟨r,i,j,hfac⟩ := routingH_factorization B e hh
  refine ⟨(g.1+r,g.2.1+i,g.2.2+j),
    ⟨g,hg,by dsimp; omega,by dsimp; omega,by dsimp; omega⟩,?_⟩
  simp only [monomialDegree,normalizedGrid,Prod.fst,Prod.snd,Nat.add_mul]
  omega

/-- Every actual cut has some M representation; this existential triple
can be off-domain, and is normalized only in the subsequent theorem. -/
theorem actual_cut_has_monomial_representation {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hMixed : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hNotch : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    {x : ℕ} (hx : x ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ z ∈ monomialClosure (canonicalIdealGenerators P.M.base R.e R.HD),
      monomialDegree P.M.base R.e z = x := by
  obtain ⟨hxH,n,hn,hnle,h,hh,heq⟩ :=
    (cyclicCut_finite_principal_reduction _ _ (routingM_pos P.M.base R.e) x).mp hx
  by_cases hprincipal : n = firstPrincipal (routingH P.M.base R.e)
      (routingM P.M.base R.e) (routingM_pos P.M.base R.e)
  · obtain ⟨delta,U,V,hdom,hform⟩ := firstPrincipal_canonical_form P.M.base R.e R.HD
    have hg : (delta,U,V) ∈ canonicalIdealGenerators P.M.base R.e R.HD :=
      Or.inr (Or.inr ⟨delta,U,V,hdom,hform,Or.inl rfl⟩)
    obtain ⟨z,hz,hdeg⟩ := generator_multiple_representation P.M.base R.e R.HD hg hh
    refine ⟨z,hz,?_⟩
    rw [hdeg]
    change normalizedGrid P.M.base R.e delta U V + h = x
    rw [←hform,←hprincipal]
    exact heq.symm
  · have hpre : n < firstPrincipal (routingH P.M.base R.e)
        (routingM P.M.base R.e) (routingM_pos P.M.base R.e) := by omega
    obtain ⟨i,j,d,_hdom,hd,hrelation,hcases,hcolon⟩ :=
      actual_preprincipal_colon_piece_exact R hMixed hNotch hn hpre
    have hpiece : x ∈ positiveReturnPiece (routingH P.M.base R.e)
        (routingM P.M.base R.e) n := ⟨hxH,hn,h,hh,heq⟩
    rw [hcolon] at hpiece
    obtain ⟨g,hg,h',hh',hxg⟩ := hpiece
    obtain ⟨zg,hzg,hdegree⟩ := colon_degree_has_monomial P.M.base R.e R.HD i j d hg
    have hgen : zg ∈ canonicalIdealGenerators P.M.base R.e R.HD :=
      Or.inr (Or.inl ⟨n,i,j,d,hn,hpre,hd,hrelation,hcases,hzg⟩)
    obtain ⟨z,hz,hdeg⟩ := generator_multiple_representation P.M.base R.e R.HD hgen hh'
    exact ⟨z,hz,by rw [hdegree] at hdeg; exact hdeg.trans hxg.symm⟩

/-- The exact R20 first-missing binder, with all numeric gates derived
from the same actual role-normalized mixed surviving-notch packet. -/
theorem actual_canonical_staircase_forward {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hMixed : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hNotch : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hdom : HerzogLShapeDomain R.HD i j)
    (hcut : normalizedGrid P.M.base R.e r i j ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    (r,i,j) ∈ monomialClosure (canonicalIdealGenerators P.M.base R.e R.HD) := by
  obtain ⟨z,hz,hdegree⟩ := actual_cut_has_monomial_representation R hMixed hNotch hcut
  obtain ⟨last,hpath,hdom',hlast⟩ := rewrite_normalizes P.M.base R.e R.HD z
  have hlastMem := monomialClosure_rewrites_preserved P.M.base R.e R.HD
    (normalized_mixed_notch_G0_G4 R hMixed hNotch).1 hpath hz
  have hlastEq : last=(r,i,j) := canonical_monomial_unique P.M.base R.e R.HD
    hdom' hdom (hlast.symm.trans hdegree)
  simpa [hlastEq] using hlastMem

theorem actual_canonical_staircase_iff {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hMixed : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hNotch : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hdom : HerzogLShapeDomain R.HD i j) :
    normalizedGrid P.M.base R.e r i j ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ↔
    (r,i,j) ∈ monomialClosure (canonicalIdealGenerators P.M.base R.e R.HD) :=
  ⟨actual_canonical_staircase_forward R hMixed hNotch r i j hdom,
    monomialClosure_degree_mem_cut P.M.base R.e R.HD⟩

theorem monomialClosure_upward {G : Set Monomial} {z z' : Monomial}
    (hz : z ∈ monomialClosure G)
    (hr : z.1 ≤ z'.1) (hi : z.2.1 ≤ z'.2.1) (hj : z.2.2 ≤ z'.2.2) :
    z' ∈ monomialClosure G := by
  obtain ⟨g,hg,hrg,hig,hjg⟩ := hz
  exact ⟨g,hg,hrg.trans hr,hig.trans hi,hjg.trans hj⟩

/-- J0 chart relations are noncanonical vectors, NOT new cut degrees. -/
def chartGenerators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Set Monomial :=
  canonicalIdealGenerators B e HD ∪
    {z | z=(0,c2 B e,0) ∨ z=(0,0,c3 B e) ∨ z=(0,cr12 HD,cr13 HD)}

theorem chart_on_domain_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial)
    (hd : HerzogLShapeDomain HD z.2.1 z.2.2) :
    z ∈ monomialClosure (chartGenerators B e HD) ↔
      z ∈ monomialClosure (canonicalIdealGenerators B e HD) := by
  constructor
  · rintro ⟨g,hg,hdiv⟩
    rcases hg with hg | hg
    · exact ⟨g,hg,hdiv⟩
    · rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;>
        rcases hd with ⟨hi,hj,hcorner⟩ <;> omega
  · rintro ⟨g,hg,hdiv⟩
    exact ⟨g,Or.inl hg,hdiv⟩

theorem actual_chart_staircase_iff {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hd : HerzogLShapeDomain R.HD i j) :
    normalizedGrid P.M.base R.e r i j ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ↔
    (r,i,j) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) :=
  (actual_canonical_staircase_iff R hm hn r i j hd).trans
    (chart_on_domain_iff P.M.base R.e R.HD (r,i,j) hd).symm

theorem actual_central_chart_redundant {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    (0,cr12 R.HD,cr13 R.HD) ∈
      monomialClosure (canonicalIdealGenerators P.M.base R.e R.HD) := by
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have gates := normalized_mixed_notch_G0_G4 R hm hn
  have hd : HerzogLShapeDomain R.HD (cr12 R.HD) (cr13 R.HD-1) :=
    ⟨by omega,by omega,Or.inr (by omega)⟩
  have hi := (normalizedGrid_mem_iff_eta_le P.M.base R.e 0
    (cr12 R.HD) (cr13 R.HD-1)).mpr (by rw [gates.2.1])
  have hc := (actual_cyclicCut_iff_routingI P.M.base R.e _).mpr hi
  have hM := actual_canonical_staircase_forward R hm hn 0 _ _ hd hc
  exact monomialClosure_upward hM (by rfl) (by rfl) (by dsimp; omega)

/-- G1 removes the central chart generator from J0 exactly, not merely
its value at one chart cell. -/
theorem actual_chart_central_generator_removable {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    monomialClosure (chartGenerators P.M.base R.e R.HD) =
    monomialClosure (canonicalIdealGenerators P.M.base R.e R.HD ∪
      {z | z=(0,c2 P.M.base R.e,0) ∨ z=(0,0,c3 P.M.base R.e)}) := by
  ext z
  constructor
  · rintro ⟨g,hg,hdiv⟩
    rcases hg with hg | hg
    · exact ⟨g,Or.inl hg,hdiv⟩
    · rcases hg with hg | hg | hg
      · exact ⟨g,Or.inr (Or.inl hg),hdiv⟩
      · exact ⟨g,Or.inr (Or.inr hg),hdiv⟩
      · subst g
        obtain ⟨g,hg,hdivg⟩ := monomialClosure_upward
          (actual_central_chart_redundant R hm hn) hdiv.1 hdiv.2.1 hdiv.2.2
        exact ⟨g,Or.inl hg,hdivg⟩
  · rintro ⟨g,hg,hdiv⟩
    rcases hg with hg | hg
    · exact ⟨g,Or.inl hg,hdiv⟩
    · rcases hg with hg | hg
      · exact ⟨g,Or.inr (Or.inl hg),hdiv⟩
      · exact ⟨g,Or.inr (Or.inr (Or.inl hg)),hdiv⟩

/-- G4 supplies an actual canonical cut properly dividing EVERY PC-shaped
vector. This is nonminimality, not fake/resource charging. -/
theorem actual_PC_proper_cut_divisor {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) (delta U : ℕ) :
    ∃ z ∈ monomialClosure (canonicalIdealGenerators P.M.base R.e R.HD),
      z.1 ≤ delta+cr31 R.HD ∧ z.2.1 ≤ U+cr32 R.HD ∧ z.2.2=0 ∧
      z ≠ (delta+cr31 R.HD,U+cr32 R.HD,0) := by
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have gates := normalized_mixed_notch_G0_G4 R hm hn
  rcases gates.2.2.2.2 with h | h
  · have hd : HerzogLShapeDomain R.HD (cr32 R.HD) 0 :=
      ⟨by omega,by omega,Or.inr (by omega)⟩
    have hi := (normalizedGrid_mem_iff_eta_le P.M.base R.e (cr31 R.HD-1)
      (cr32 R.HD) 0).mpr (by omega)
    have hc := (actual_cyclicCut_iff_routingI P.M.base R.e _).mpr hi
    have hM := actual_canonical_staircase_forward R hm hn _ _ _ hd hc
    refine ⟨(cr31 R.HD-1,cr32 R.HD,0),hM,by dsimp; omega,
      by dsimp; omega,rfl,?_⟩
    intro heq
    have hx := congrArg Prod.fst heq
    simp only [Prod.fst] at hx
    omega
  · have hd : HerzogLShapeDomain R.HD (cr32 R.HD-1) 0 :=
      ⟨by omega,by omega,Or.inr (by omega)⟩
    have hi := (normalizedGrid_mem_iff_eta_le P.M.base R.e (cr31 R.HD)
      (cr32 R.HD-1) 0).mpr h
    have hc := (actual_cyclicCut_iff_routingI P.M.base R.e _).mpr hi
    have hM := actual_canonical_staircase_forward R hm hn _ _ _ hd hc
    refine ⟨(cr31 R.HD,cr32 R.HD-1,0),hM,by dsimp; omega,
      by dsimp; omega,rfl,?_⟩
    intro heq
    have hx := congrArg (fun z : Monomial => z.2.1) heq
    simp only [Prod.fst,Prod.snd] at hx
    omega

end NS25Lean.L5A2C4OR21
