import NS25Lean.P2Sectors

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2B

open NS25Lean.L5A1

variable {Gamma : NumericalSemigroup}

/-! ### Raw finite-routing accounting -/

/-- The raw finite-routing identity `W = C_br - U - E`, with all four
counting equalities exposed as hypotheses. -/
theorem raw_routing_identity
    (S B M T E Ab C U t : ℤ)
    (hT : T = S + B - M) (ht : t = T - E)
    (hB : B = Ab + C) (hM : M = Ab + U) :
    t - S = C - U - E := by
  omega

/-- ENTRY converts the raw identity into one more exposed branch than the
available unused-merge and fake/external seats. -/
theorem entry_unpaid_channel
    (C U E W : ℤ) (hW : W = C - U - E) (hentry : W = 1) :
    C = U + E + 1 := by
  omega

/-! ### Herzog L-shape and inverse-boundary canonicalization -/

/-- The standard Herzog `a`-Apéry L-shape, written with the coefficient
decompositions `c₂ = pH + zH` and `c₃ = qH + vH` already substituted. -/
def InLShape (pH qH zH vH i j : ℤ) : Prop :=
  0 ≤ i ∧ 0 ≤ j ∧ i < pH + zH ∧ j < qH + vH ∧ (i < pH ∨ j < qH)

/-- A coordinate point represents residue zero modulo `a`.  The integer
witness is intentional: the canonicalization proof subtracts Herzog
relations and therefore does not require truncated natural subtraction. -/
def RepresentsZero (a b c i j : ℤ) : Prop :=
  ∃ k : ℤ, i * b + j * c = k * a

/-- The canonical L-shape has `(0,0)` as its only zero-residue point. -/
def UniqueZeroInLShape (a b c pH qH zH vH : ℤ) : Prop :=
  ∀ i j, InLShape pH qH zH vH i j → RepresentsZero a b c i j → i = 0 ∧ j = 0

/-- First inverse-boundary alternative for a strict right-bottom arm. -/
theorem inverse_boundary_first_rb
    (a b c c1 pH qH zH vH I J s tau : ℤ)
    (hp : 0 < pH) (hq : 0 < qH) (hz : 0 < zH) (hv : 0 < vH)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hs : 1 ≤ s ∧ s < zH) (htau : 1 ≤ tau ∧ tau < qH)
    (hrel : pH * b + qH * c = c1 * a)
    (hzero : RepresentsZero a b c (pH + s + I) (tau + J))
    (hunique : UniqueZeroInLShape a b c pH qH zH vH) :
    1 ≤ I ∨ qH ≤ J := by
  by_contra hn
  push_neg at hn
  have hI0 : I = 0 := by omega
  subst I
  rcases hzero with ⟨k, hk⟩
  by_cases hsum : tau + J < qH
  · have hshape : InLShape pH qH zH vH (pH + s) (tau + J) := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inr hsum
    have hzrep : RepresentsZero a b c (pH + s) (tau + J) := ⟨k, by simpa using hk⟩
    have h00 := hunique _ _ hshape hzrep
    omega
  · have hshape : InLShape pH qH zH vH s (tau + J - qH) := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inr (by omega)
    have hzrep : RepresentsZero a b c s (tau + J - qH) := by
      refine ⟨k - c1, ?_⟩
      have hsub : tau + J - qH + qH = tau + J := by omega
      have hk' : (pH + s) * b + (tau + J) * c = k * a := by simpa using hk
      calc
        s * b + (tau + J - qH) * c
            = (pH + s) * b + (tau + J) * c - (pH * b + qH * c) := by
                rw [← hsub]
                ring
        _ = k * a - c1 * a := by rw [hk', hrel]
        _ = (k - c1) * a := by ring
    have h00 := hunique _ _ hshape hzrep
    omega

/-- First inverse-boundary alternative for a strict left-top arm. -/
theorem inverse_boundary_first_lt
    (a b c wH pH qH zH vH I J s tau : ℤ)
    (hp : 0 < pH) (hq : 0 < qH) (hz : 0 < zH) (hv : 0 < vH)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hs : 1 ≤ s ∧ s < pH) (htau : 1 ≤ tau ∧ tau < vH)
    (hrel : (qH + vH) * c = wH * a + zH * b)
    (hzero : RepresentsZero a b c (s + I) (qH + tau + J))
    (hunique : UniqueZeroInLShape a b c pH qH zH vH) :
    1 ≤ I ∨ qH ≤ J := by
  by_contra hn
  push_neg at hn
  have hI0 : I = 0 := by omega
  subst I
  rcases hzero with ⟨k, hk⟩
  by_cases hsum : tau + J < vH
  · have hshape : InLShape pH qH zH vH s (qH + tau + J) := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inl hs.2
    have hzrep : RepresentsZero a b c s (qH + tau + J) := ⟨k, by simpa using hk⟩
    have h00 := hunique _ _ hshape hzrep
    omega
  · have hshape : InLShape pH qH zH vH (s + zH) (tau + J - vH) := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inr (by omega)
    have hzrep : RepresentsZero a b c (s + zH) (tau + J - vH) := by
      refine ⟨k - wH, ?_⟩
      have hsub : tau + J - vH + vH = tau + J := by omega
      have hk' : s * b + (qH + tau + J) * c = k * a := by simpa using hk
      calc
        (s + zH) * b + (tau + J - vH) * c
            = s * b + (qH + tau + J) * c - ((qH + vH) * c - zH * b) := by
                rw [← hsub]
                ring
        _ = k * a - wH * a := by
          rw [hk']
          nlinarith [hrel]
        _ = (k - wH) * a := by ring
    have h00 := hunique _ _ hshape hzrep
    omega

/-- Second inverse-boundary alternative for a strict right-bottom arm. -/
theorem inverse_boundary_second_rb
    (a b c uH pH qH zH vH I J s tau : ℤ)
    (hp : 0 < pH) (hq : 0 < qH) (hz : 0 < zH) (hv : 0 < vH)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hs : 1 ≤ s ∧ s < zH) (htau : 1 ≤ tau ∧ tau < qH)
    (hrel : (pH + zH) * b = uH * a + vH * c)
    (hzero : RepresentsZero a b c (pH + s + I) (tau + J))
    (hunique : UniqueZeroInLShape a b c pH qH zH vH) :
    1 ≤ J ∨ pH ≤ I := by
  by_contra hn
  push_neg at hn
  have hJ0 : J = 0 := by omega
  subst J
  rcases hzero with ⟨k, hk⟩
  by_cases hsum : pH + s + I < pH + zH
  · have hshape : InLShape pH qH zH vH (pH + s + I) tau := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · exact hsum
      constructor
      · omega
      · exact Or.inr htau.2
    have hzrep : RepresentsZero a b c (pH + s + I) tau := ⟨k, by simpa using hk⟩
    have h00 := hunique _ _ hshape hzrep
    omega
  · have hshape : InLShape pH qH zH vH (s + I - zH) (tau + vH) := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inl (by omega)
    have hzrep : RepresentsZero a b c (s + I - zH) (tau + vH) := by
      refine ⟨k - uH, ?_⟩
      have hsub : s + I - zH + zH = s + I := by omega
      have hk' : (pH + s + I) * b + tau * c = k * a := by simpa using hk
      calc
        (s + I - zH) * b + (tau + vH) * c
            = (pH + s + I) * b + tau * c - ((pH + zH) * b - vH * c) := by
                rw [← hsub]
                ring
        _ = k * a - uH * a := by
          rw [hk']
          nlinarith [hrel]
        _ = (k - uH) * a := by ring
    have h00 := hunique _ _ hshape hzrep
    omega

/-- Second inverse-boundary alternative for a strict left-top arm. -/
theorem inverse_boundary_second_lt
    (a b c c1 pH qH zH vH I J s tau : ℤ)
    (hp : 0 < pH) (hq : 0 < qH) (hz : 0 < zH) (hv : 0 < vH)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hs : 1 ≤ s ∧ s < pH) (htau : 1 ≤ tau ∧ tau < vH)
    (hrel : pH * b + qH * c = c1 * a)
    (hzero : RepresentsZero a b c (s + I) (qH + tau + J))
    (hunique : UniqueZeroInLShape a b c pH qH zH vH) :
    1 ≤ J ∨ pH ≤ I := by
  by_contra hn
  push_neg at hn
  have hJ0 : J = 0 := by omega
  subst J
  rcases hzero with ⟨k, hk⟩
  by_cases hsum : s + I < pH
  · have hshape : InLShape pH qH zH vH (s + I) (qH + tau) := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inl hsum
    have hzrep : RepresentsZero a b c (s + I) (qH + tau) := ⟨k, by simpa using hk⟩
    have h00 := hunique _ _ hshape hzrep
    omega
  · have hshape : InLShape pH qH zH vH (s + I - pH) tau := by
      unfold InLShape
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact Or.inl (by omega)
    have hzrep : RepresentsZero a b c (s + I - pH) tau := by
      refine ⟨k - c1, ?_⟩
      have hsub : s + I - pH + pH = s + I := by omega
      have hk' : (s + I) * b + (qH + tau) * c = k * a := by simpa using hk
      calc
        (s + I - pH) * b + tau * c
            = (s + I) * b + (qH + tau) * c - (pH * b + qH * c) := by
                rw [← hsub]
                ring
        _ = k * a - c1 * a := by rw [hk', hrel]
        _ = (k - c1) * a := by ring
    have h00 := hunique _ _ hshape hzrep
    omega

/-- The exact first inverse-boundary conclusion, combining the two frozen
strict-arm orientations. -/
theorem inverse_boundary_first
    (a b c c1 wH pH qH zH vH I J : ℤ)
    (hp : 0 < pH) (hq : 0 < qH) (hz : 0 < zH) (hv : 0 < vH)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hrel1 : pH * b + qH * c = c1 * a)
    (hrel3 : (qH + vH) * c = wH * a + zH * b)
    (hunique : UniqueZeroInLShape a b c pH qH zH vH)
    (harm :
      (∃ s tau, 1 ≤ s ∧ s < zH ∧ 1 ≤ tau ∧ tau < qH ∧
        RepresentsZero a b c (pH + s + I) (tau + J)) ∨
      (∃ s tau, 1 ≤ s ∧ s < pH ∧ 1 ≤ tau ∧ tau < vH ∧
        RepresentsZero a b c (s + I) (qH + tau + J))) :
    1 ≤ I ∨ qH ≤ J := by
  rcases harm with ⟨s, tau, hs0, hsz, ht0, htq, hzero⟩ |
      ⟨s, tau, hs0, hsp, ht0, htv, hzero⟩
  · exact inverse_boundary_first_rb a b c c1 pH qH zH vH I J s tau hp hq hz hv
      hI hJ ⟨hs0, hsz⟩ ⟨ht0, htq⟩ hrel1 hzero hunique
  · exact inverse_boundary_first_lt a b c wH pH qH zH vH I J s tau hp hq hz hv
      hI hJ ⟨hs0, hsp⟩ ⟨ht0, htv⟩ hrel3 hzero hunique

/-- The exact second inverse-boundary conclusion, combining the two frozen
strict-arm orientations. -/
theorem inverse_boundary_second
    (a b c c1 uH pH qH zH vH I J : ℤ)
    (hp : 0 < pH) (hq : 0 < qH) (hz : 0 < zH) (hv : 0 < vH)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (hrel1 : pH * b + qH * c = c1 * a)
    (hrel2 : (pH + zH) * b = uH * a + vH * c)
    (hunique : UniqueZeroInLShape a b c pH qH zH vH)
    (harm :
      (∃ s tau, 1 ≤ s ∧ s < zH ∧ 1 ≤ tau ∧ tau < qH ∧
        RepresentsZero a b c (pH + s + I) (tau + J)) ∨
      (∃ s tau, 1 ≤ s ∧ s < pH ∧ 1 ≤ tau ∧ tau < vH ∧
        RepresentsZero a b c (s + I) (qH + tau + J))) :
    1 ≤ J ∨ pH ≤ I := by
  rcases harm with ⟨s, tau, hs0, hsz, ht0, htq, hzero⟩ |
      ⟨s, tau, hs0, hsp, ht0, htv, hzero⟩
  · exact inverse_boundary_second_rb a b c uH pH qH zH vH I J s tau hp hq hz hv
      hI hJ ⟨hs0, hsz⟩ ⟨ht0, htq⟩ hrel2 hzero hunique
  · exact inverse_boundary_second_lt a b c c1 pH qH zH vH I J s tau hp hq hz hv
      hI hJ ⟨hs0, hsp⟩ ⟨ht0, htv⟩ hrel1 hzero hunique

/-! ### Signed OX/OY exclusion -/

/-- The OX signed seam: an earlier origin carver and the canonical transport
bound put the endpoint candidate strictly below the OX gate height. -/
theorem ox_signed_candidate_lt
    (c1 uH wH R0 Rx : ℤ)
    (hc1 : c1 = uH + wH) (horigin : R0 < c1)
    (htransport : Rx - wH ≤ R0 - c1) :
    Rx < wH := by
  omega

/-- Therefore the same candidate contradicts the numerical OX escape
requirement that every legal endpoint candidate be at least `wH`. -/
theorem ox_escape_impossible
    (c1 uH wH R0 Rx : ℤ)
    (hc1 : c1 = uH + wH) (horigin : R0 < c1)
    (htransport : Rx - wH ≤ R0 - c1)
    (hescape : wH ≤ Rx) : False := by
  have := ox_signed_candidate_lt c1 uH wH R0 Rx hc1 horigin htransport
  omega

/-- The dual OY signed seam. -/
theorem oy_signed_candidate_lt
    (c1 uH wH R0 Ry : ℤ)
    (hc1 : c1 = uH + wH) (horigin : R0 < c1)
    (htransport : Ry - uH ≤ R0 - c1) :
    Ry < uH := by
  omega

/-- The dual OY escape exclusion. -/
theorem oy_escape_impossible
    (c1 uH wH R0 Ry : ℤ)
    (hc1 : c1 = uH + wH) (horigin : R0 < c1)
    (htransport : Ry - uH ≤ R0 - c1)
    (hescape : uH ≤ Ry) : False := by
  have := oy_signed_candidate_lt c1 uH wH R0 Ry hc1 horigin htransport
  omega

/-! ### Fixed-base checkpoint -/

/-- Once the actual Sector-B construction excludes ENTRY, the requested
fixed-base inequality follows immediately from the frozen L5-A1 ENTRY theorem.
This theorem deliberately keeps the still-missing bridge hypothesis visible. -/
theorem sectorB_type_le_sourceCount_of_entry_exclusion
    (P : P2Data Gamma) (_hB : SectorB P.M) (hentry : P.W ≠ 1) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  by_contra hfail
  exact hentry (p2_entry P hfail)

end NS25Lean.L5A2B
