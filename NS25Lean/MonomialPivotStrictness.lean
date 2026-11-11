import NS25Lean.MonomialTwoAxisRigidity
import NS25Lean.MonomialComponentBound

set_option linter.style.header false
noncomputable section
namespace NS25Lean.MonomialPivotStrictness
open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C L5A1 L5A2R49First
variable {Gamma : NumericalSemigroup}

/-- Distinct minimal powers on a fixed axis have comparable exponents, hence
cannot both be minimal. The equality here is numerical degree equality. -/
theorem same_axis_minimal_degree (k : Type*) [Field k] (B : Data Gamma)
    (i : Fin 3) (a b : ℕ)
    (ha : Finsupp.single i a∈minimalExponents (B.J k))
    (hb : Finsupp.single i b∈minimalExponents (B.J k)) :
    a*weights B i=b*weights B i := by
  rcases le_total a b with hab | hba
  · have hle : Finsupp.single i a≤Finsupp.single i b :=
      Finsupp.single_le_iff.mpr (by simpa using hab)
    have he := le_antisymm hle (hb.2 ha.1 hle)
    simpa only [weight_single] using congrArg (weight B) he
  · have hle : Finsupp.single i b≤Finsupp.single i a :=
      Finsupp.single_le_iff.mpr (by simpa using hba)
    have he := le_antisymm (ha.2 hb.1 hle) hle
    simpa only [weight_single] using congrArg (weight B) he

/-- All positive actual component contributions occur at one numerical degree.
This is a theorem from the actual fibers, not a field in an interface. -/
theorem monomial_positive_degree_unique (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (hJ : IsMonomialIdeal k (M.base.J k))
    (g : Exponent) (hg : g∈fullSupportGenerators (M.base.J k))
    (h d : ℕ) (hh : 0<fiberContribution M h) (hd : 0<fiberContribution M d) : h=d := by
  by_contra hne
  obtain ⟨i,A,v,hA,hdeg,hmin,hvi,hv⟩ := positive_has_nonunique_pure k M hJ g hg h hh
  obtain ⟨j,B,w,hB,ddeg,dmin,hwj,hw⟩ := positive_has_nonunique_pure k M hJ g hg d hd
  have hij : i≠j := by
    intro he
    subst j
    exact hne (hdeg.trans ((same_axis_minimal_degree k M.base i A B hmin dmin).trans ddeg.symm))
  exact two_axis_distinct_degree_impossible k M.base hJ g hg i j A B hA hB hij
    (by rwa [←hdeg,←ddeg]) hmin dmin v w hvi hwj (hv.trans hdeg) (hw.trans ddeg)

/-- The finite actual component identity, the proved unique positive degree,
and the proved local bound give the strictness core. -/
theorem multiplicity_full_support_defect_le_one (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (hJ : IsMonomialIdeal k (M.base.J k))
    (g : Exponent) (hg : g∈fullSupportGenerators (M.base.J k)) :
    chosenDefect M.base≤1 := by
  classical
  rw [chosenDefect_eq_contribution_sum M]
  by_cases hex : ∃ h∈activeDegreeFinset M, 0<fiberContribution M h
  · obtain ⟨h,hh,hp⟩ := hex
    have hs : ∑ d∈activeDegreeFinset M, fiberContribution M d=fiberContribution M h := by
      apply Finset.sum_eq_single h
      · intro d hd hdh
        by_contra hn
        exact hdh (monomial_positive_degree_unique k M hJ g hg d h (by omega) hp)
      · exact fun hn => (hn hh).elim
    rw [hs]
    exact monomial_contribution_le_one k M hJ g hg h
  · push Not at hex
    have hs : ∑ d∈activeDegreeFinset M, fiberContribution M d=0 :=
      Finset.sum_eq_zero (fun d hd => Nat.eq_zero_of_le_zero (hex d hd))
    omega

/-- The manuscript's common original-pivot monomial strictness proposition.
The internal multiplicity proof is transferred through literal equality of
the actual polynomial ideals and exact equality of the original defect.
There is no assumption that the original q is the multiplicity. -/
theorem original_pivot_full_support_defect_le_one (k : Type*) [Field k]
    (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k))
    (g : Exponent) (hg : g∈fullSupportGenerators (B.J k)) : chosenDefect B≤1 := by
  have hideal : (transferBase B).base.J k=B.J k :=
    dilatedData_J k B (transferScale B) (transferScale_gt B) (transferScale_coprime B)
  have hdefect : chosenDefect (transferBase B).base=chosenDefect B :=
    dilation_defect B (transferScale B) (transferScale_gt B) (transferScale_coprime B)
  have hmono : IsMonomialIdeal k ((transferBase B).base.J k) := by rwa [hideal]
  have hfull : g∈fullSupportGenerators ((transferBase B).base.J k) := by rwa [hideal]
  rw [←hdefect]
  exact multiplicity_full_support_defect_le_one k (transferBase B) hmono g hfull

theorem original_pivot_monomial_q_fs_zero (k : Type*) [Field k]
    (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k)) (hp : 2≤chosenDefect B) :
    q_fs (B.J k)=0 := by
  rw [q_fs,Set.ncard_eq_zero (hs := fullSupportGenerators_finite _)]
  ext g
  simp only [Set.mem_empty_iff_false,iff_false]
  intro hg
  have hle := original_pivot_full_support_defect_le_one k B hJ g hg
  omega

/-- The original ideal and original rho occur in the strong type conclusion. -/
theorem original_pivot_monomial_strict_type (k : Type*) [Field k]
    (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k)) (hp : 2≤chosenDefect B) :
    Gamma.asRelativeIdeal.idealType≤Presentation.rho Gamma-2 := by
  have hb := support_refined_monomial_type_bound
    (chosenArtinianMonomial B MonomialOrder.degLex hJ)
  change quotientType (B.J k)≤mu (B.J k)+q_fs (B.J k)-2 at hb
  rw [chosen_type_eq,chosen_mu_eq,original_pivot_monomial_q_fs_zero k B hJ hp] at hb
  simpa using hb

end NS25Lean.MonomialPivotStrictness
