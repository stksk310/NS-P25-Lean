import NS25Lean.OneDefectFrontend

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C.FerrersAudit
open MvPolynomial
abbrev Exp := Fin 2 →₀ ℕ
abbrev Poly := MvPolynomial (Fin 2) ℚ

def axisIdeal (P Q : ℕ) : Ideal Poly :=
  Ideal.span ((fun u : Exp => monomial u (1 : ℚ)) ''
    {u | u = Finsupp.single 0 P ∨ u = Finsupp.single 1 Q})

theorem axis_mem (P Q : ℕ) (u : Exp) :
    monomial u (1 : ℚ) ∈ axisIdeal P Q ↔ P ≤ u 0 ∨ Q ≤ u 1 := by
  classical
  simp [axisIdeal, mem_ideal_span_monomial_image, Finsupp.single_le_iff]

def std (I : Ideal Poly) : Set Exp := {u | monomial u (1 : ℚ) ∉ I}

theorem axis_cofinite (P Q : ℕ) : (std (axisIdeal P Q)).Finite := by
  let f : std (axisIdeal P Q) → Fin P × Fin Q := fun u =>
    ⟨⟨u.val 0, by
        have hu := u.property
        change monomial u.val (1 : ℚ) ∉ axisIdeal P Q at hu
        rw [axis_mem] at hu
        omega⟩,
     ⟨u.val 1, by
        have hu := u.property
        change monomial u.val (1 : ℚ) ∉ axisIdeal P Q at hu
        rw [axis_mem] at hu
        omega⟩⟩
  have hi : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    ext j
    fin_cases j
    · exact congrArg (fun t : Fin P × Fin Q => t.1.val) he
    · exact congrArg (fun t : Fin P × Fin Q => t.2.val) he
  haveI := Finite.of_injective f hi
  exact Set.toFinite _

theorem axis_minimal_pure (P Q : ℕ) (u : Exp)
    (hu : Minimal (fun v => monomial v (1 : ℚ) ∈ axisIdeal P Q) u) :
    u 0 = 0 ∨ u 1 = 0 := by
  classical
  rcases (axis_mem P Q u).mp hu.1 with hp | hq
  · have hm : monomial (Finsupp.single 0 P) (1 : ℚ) ∈ axisIdeal P Q :=
      (axis_mem P Q _).mpr (Or.inl (by simp))
    have he := le_antisymm (hu.2 hm (Finsupp.single_le_iff.mpr hp))
      (Finsupp.single_le_iff.mpr hp)
    right
    rw [he]
    simp
  · have hm : monomial (Finsupp.single 1 Q) (1 : ℚ) ∈ axisIdeal P Q :=
      (axis_mem P Q _).mpr (Or.inr (by simp))
    have he := le_antisymm (hu.2 hm (Finsupp.single_le_iff.mpr hq))
      (Finsupp.single_le_iff.mpr hq)
    left
    rw [he]
    simp

def height (P Q r : ℕ) : ℕ := if r < P then Q else 0

/-- This identifies the declared heights with the actual monomial ideals, not a drawing. -/
theorem height_membership (P Q r s : ℕ) :
    monomial (Finsupp.single 0 r + Finsupp.single 1 s) (1 : ℚ) ∈ axisIdeal P Q ↔
      height P Q r ≤ s := by
  rw [axis_mem]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  norm_num
  unfold height
  split_ifs <;> omega

theorem height_antitone (P Q : ℕ) : Antitone (height P Q) := by
  intro r s hrs
  unfold height
  split_ifs <;> omega

theorem counterexample_inclusion : axisIdeal 3 3 ≤ axisIdeal 1 3 := by
  apply Ideal.span_le.mpr
  rintro _ ⟨u, hu | hu, rfl⟩ <;> subst u
  · exact (axis_mem 1 3 _).mpr (Or.inl (by simp))
  · exact (axis_mem 1 3 _).mpr (Or.inr (by simp))

/-- The discrepancy is exactly the nonempty connected block of columns 1,2. -/
theorem counterexample_discrepancy (r : ℕ) :
    height 1 3 r < height 3 3 r ↔ 1 ≤ r ∧ r ≤ 2 := by
  unfold height
  split_ifs <;> omega

theorem counterexample_agreement :
    height 1 3 0 = height 3 3 0 ∧ height 1 3 3 = height 3 3 3 := by decide

theorem counterexample_order (r : ℕ) : height 1 3 r ≤ height 3 3 r := by
  unfold height
  split_ifs <;> omega

theorem counterexample_no_mixed_generator :
    ¬ ∃ u : Exp, Minimal (fun v => monomial v (1 : ℚ) ∈ axisIdeal 1 3) u ∧
      monomial u (1 : ℚ) ∉ axisIdeal 3 3 ∧ 0 < u 0 ∧ 0 < u 1 := by
  rintro ⟨u, hu, _, hy, hz⟩
  rcases axis_minimal_pure 1 3 u hu with he | he <;> omega

/-- Valid positive-height repair: pure clips cannot give a discrepancy between
two agreement columns if the right agreement has positive height. -/
theorem pure_clips_no_positive_bounded_lens (D : ℕ → ℕ) (hD : Antitone D)
    (P Q l r t : ℕ) (hlt : l < t) (htr : t < r)
    (hleft : (if l < P then min (D l) Q else 0) = D l)
    (hright : (if r < P then min (D r) Q else 0) = D r)
    (hrpos : 0 < D r) : (if t < P then min (D t) Q else 0) = D t := by
  have hrP : r < P := by split_ifs at hright <;> omega
  have htP : t < P := by omega
  have hlP : l < P := by omega
  rw [if_pos hlP] at hleft
  rw [if_pos htP]
  have hDlQ : D l ≤ Q := by omega
  have hDtDl := hD (Nat.le_of_lt hlt)
  exact min_eq_left (by omega)

/-- The exact valid local replacement used between common cut corners. Any
removed standard monomial strictly below the relevant two corner coordinates
has an effective mixed minimal killer. Axis endpoints are included. -/
theorem mixed_killer_between_common_corners {k : Type*} [Field k]
    (A J : Ideal (MvPolynomial (Fin 2) k)) (u v t : Exp)
    (hu : Minimal (fun w => monomial w (1 : k) ∈ J) u)
    (hv : Minimal (fun w => monomial w (1 : k) ∈ J) v)
    (htA : monomial t (1 : k) ∉ A) (htJ : monomial t (1 : k) ∈ J)
    (htx : t 0 < v 0) (hty : t 1 < u 1) :
    ∃ w : Exp, w ≤ t ∧ Minimal (fun z => monomial z (1 : k) ∈ J) w ∧
      monomial w (1 : k) ∉ A ∧ 0 < w 0 ∧ 0 < w 1 := by
  obtain ⟨w, hwt, hw⟩ := (Set.isPWO_of_wellQuasiOrderedLE
    {z : Exp | monomial z (1 : k) ∈ J}).exists_le_minimal htJ
  refine ⟨w, hwt, hw, ?_, ?_, ?_⟩
  · intro hwA
    exact htA (A.mem_of_dvd (monomial_one_dvd_monomial_one.mpr hwt) hwA)
  · by_contra hn
    have hw0 : w 0 = 0 := by omega
    have hwu : w ≤ u := by
      intro i
      fin_cases i
      · simp [hw0]
      · exact (hwt 1).trans hty.le
    have hle := hu.2 hw.1 hwu
    have := hle 1
    have := hwt 1
    omega
  · by_contra hn
    have hw1 : w 1 = 0 := by omega
    have hwv : w ≤ v := by
      intro i
      fin_cases i
      · exact (hwt 0).trans htx.le
      · simp [hw1]
    have hle := hv.2 hw.1 hwv
    have := hle 0
    have := hwt 0
    omega

end NS25Lean.L3C.FerrersAudit
