import NS25Lean.P2SectorBActualRouting

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR1

open FourGeneratedBridge ChosenBase

variable {Gamma H : NumericalSemigroup}

/-- The source-exact return ideal `J_n = H ∩ (n + H)`. -/
def returnIdeal (H : NumericalSemigroup) (n : ℕ) : RelativeIdeal H where
  carrier := {z | z ∈ H.asRelativeIdeal ∧ z ∈ H.asRelativeIdeal.translate n}
  nonempty := by
    obtain ⟨u, hu⟩ := H.asRelativeIdeal.exists_tail
    obtain ⟨v, hv⟩ := (H.asRelativeIdeal.translate n).exists_tail
    refine ⟨max u v, hu _ (le_max_left _ _), hv _ (le_max_right _ _)⟩
  bddBelow := by
    obtain ⟨u, hu⟩ := H.asRelativeIdeal.bddBelow
    exact ⟨u, fun _ hz => hu hz.1⟩
  add_mem := by
    intro z h hz hh
    exact ⟨H.asRelativeIdeal.add_mem hz.1 hh,
      (H.asRelativeIdeal.translate n).add_mem hz.2 hh⟩

@[simp] theorem mem_returnIdeal_iff (H : NumericalSemigroup) (n : ℕ) (z : ℤ) :
    z ∈ returnIdeal H n ↔ z ∈ H.asRelativeIdeal ∧ z - n ∈ H.asRelativeIdeal :=
  Iff.rfl

/-- The nonprincipal prefix `K^- = ⋃_{0 < ell < q0} J_(ell*m)`.
It is kept as a set because it is honestly empty when `q0 ≤ 1`. -/
def prefixCarrier (H : NumericalSemigroup) (m q0 : ℕ) : Set ℤ :=
  {z | ∃ ell : ℕ, 0 < ell ∧ ell < q0 ∧ z ∈ returnIdeal H (ell * m)}

@[simp] theorem mem_prefixCarrier_iff (H : NumericalSemigroup) (m q0 : ℕ) (z : ℤ) :
    z ∈ prefixCarrier H m q0 ↔
      ∃ ell : ℕ, 0 < ell ∧ ell < q0 ∧ z ∈ returnIdeal H (ell * m) :=
  Iff.rfl

/-- The principal-inserted set `K = K^- ∪ (q0*m + H)`. -/
def finalCarrier (H : NumericalSemigroup) (m q0 : ℕ) : Set ℤ :=
  prefixCarrier H m q0 ∪ (H.asRelativeIdeal.translate (q0 * m)).carrier

/-- The untruncated union of all positive return levels. -/
def positiveReturnCarrier (H : NumericalSemigroup) (m : ℕ) : Set ℤ :=
  {z | ∃ ell : ℕ, 0 < ell ∧ z ∈ returnIdeal H (ell * m)}

@[simp] theorem mem_finalCarrier_iff (H : NumericalSemigroup) (m q0 : ℕ) (z : ℤ) :
    z ∈ finalCarrier H m q0 ↔
      z ∈ prefixCarrier H m q0 ∨ z - q0 * m ∈ H.asRelativeIdeal :=
  Iff.rfl

/-- Minimal `H`-source of an arbitrary integer carrier. -/
def IsSource (H : NumericalSemigroup) (K : Set ℤ) (s : ℤ) : Prop :=
  s ∈ K ∧ ∀ h : ℕ, h ∈ H → h ≠ 0 → s - h ∉ K

theorem isSource_returnIdeal_iff (H : NumericalSemigroup) (n : ℕ) (s : ℤ) :
    IsSource H (returnIdeal H n).carrier s ↔ (returnIdeal H n).IsMinimalGenerator s :=
  Iff.rfl

/-- Minimal source of the final carrier that is not the newly inserted
principal source.  This is exactly the source-level content of BRANCH-BIRTH
needed by M1; no branch-incidence or later transport datum is added. -/
def IsBranchBirth (H : NumericalSemigroup) (m q0 : ℕ) (s : ℤ) : Prop :=
  IsSource H (finalCarrier H m q0) s ∧ s ≠ (q0 * m : ℕ)

/-- M1: an old final source belongs to, and remains minimal in, the prefix. -/
theorem branchBirth_isPrefixSource {H : NumericalSemigroup} {m q0 : ℕ} {s : ℤ}
    (hs : IsBranchBirth H m q0 s) : IsSource H (prefixCarrier H m q0) s := by
  rcases hs with ⟨⟨hsK, hsmin⟩, hsprincipal⟩
  have hsprefix : s ∈ prefixCarrier H m q0 := by
    rcases hsK with hprefix | hprincipal
    · exact hprefix
    · change s - (q0 * m : ℕ) ∈ H.asRelativeIdeal at hprincipal
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hprincipal
      obtain ⟨h, hhH, heq⟩ := hprincipal
      have hrepr : s = (q0 * m : ℕ) + h := by omega
      have hh0 : h ≠ 0 := by
        intro hz
        subst h
        simp at hrepr
        exact hsprincipal hrepr
      exfalso
      apply (hsmin h hhH hh0)
      right
      change (s - (h : ℤ)) - (q0 * m : ℕ) ∈ H.asRelativeIdeal
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      exact ⟨0, H.zero_mem, by rw [hrepr]; simp⟩
  refine ⟨hsprefix, ?_⟩
  intro h hhH hh0 hsub
  exact hsmin h hhH hh0 (Or.inl hsub)

/-- A source of the prefix is an individual source of at least one return
ideal that contains it.  No uniqueness of return provenance is asserted. -/
theorem prefixSource_has_returnWitness {H : NumericalSemigroup} {m q0 : ℕ} {s : ℤ}
    (hs : IsSource H (prefixCarrier H m q0) s) :
    ∃ ell : ℕ, 0 < ell ∧ ell < q0 ∧ (returnIdeal H (ell * m)).IsMinimalGenerator s := by
  obtain ⟨ell, hellpos, helllt, hsJ⟩ := hs.1
  refine ⟨ell, hellpos, helllt, hsJ, ?_⟩
  intro h hhH hh0 hsub
  exact hs.2 h hhH hh0 ⟨ell, hellpos, helllt, hsub⟩

/-- The canonical return witness set `Lambda(s)`. -/
def ReturnWitness (H : NumericalSemigroup) (m q0 : ℕ) (s : ℤ) (ell : ℕ) : Prop :=
  0 < ell ∧ ell < q0 ∧ (returnIdeal H (ell * m)).IsMinimalGenerator s

/-- `ell_*(s) = min Lambda(s)`, defined only from a proof that `s` is a
prefix source. -/
def canonicalReturnIndex {H : NumericalSemigroup} {m q0 : ℕ} {s : ℤ}
    (hs : IsSource H (prefixCarrier H m q0) s) : ℕ := by
  classical
  exact Nat.find (prefixSource_has_returnWitness hs)

theorem canonicalReturnIndex_spec {H : NumericalSemigroup} {m q0 : ℕ} {s : ℤ}
    (hs : IsSource H (prefixCarrier H m q0) s) :
    ReturnWitness H m q0 s (canonicalReturnIndex hs) := by
  classical
  exact Nat.find_spec (prefixSource_has_returnWitness hs)

theorem canonicalReturnIndex_min {H : NumericalSemigroup} {m q0 ell : ℕ} {s : ℤ}
    (hs : IsSource H (prefixCarrier H m q0) s)
    (hell : ReturnWitness H m q0 s ell) :
    canonicalReturnIndex hs ≤ ell := by
  classical
  exact Nat.find_min' (prefixSource_has_returnWitness hs) hell

/-- Positive multiples of `m` eventually enter every numerical semigroup. -/
theorem exists_positive_multiple_mem (H : NumericalSemigroup) {m : ℕ} (hm : 0 < m) :
    ∃ ell : ℕ, 0 < ell ∧ ell * m ∈ H := by
  obtain ⟨c, hc⟩ := H.exists_conductor
  refine ⟨c + 1, by omega, hc ((c + 1) * m) ?_⟩
  nlinarith

/-- The first positive return level `q0`. -/
def principalIndex (H : NumericalSemigroup) (m : ℕ) (hm : 0 < m) : ℕ :=
  by
    classical
    exact Nat.find (exists_positive_multiple_mem H hm)

theorem principalIndex_spec (H : NumericalSemigroup) (m : ℕ) (hm : 0 < m) :
    0 < principalIndex H m hm ∧ principalIndex H m hm * m ∈ H := by
  classical
  exact Nat.find_spec (exists_positive_multiple_mem H hm)

theorem principalIndex_min (H : NumericalSemigroup) (m : ℕ) (hm : 0 < m)
    {ell : ℕ} (hellpos : 0 < ell) (hellH : ell * m ∈ H) :
    principalIndex H m hm ≤ ell := by
  classical
  exact Nat.find_min' (exists_positive_multiple_mem H hm) ⟨hellpos, hellH⟩

/-- Once the first principal return `q0*m ∈ H` is reached, every positive
return level reduces either to a strict prefix level or to the principal
translate. -/
theorem positiveReturnCarrier_eq_finalCarrier (H : NumericalSemigroup) (m : ℕ)
    (hm : 0 < m) :
    positiveReturnCarrier H m = finalCarrier H m (principalIndex H m hm) := by
  let q0 := principalIndex H m hm
  have hq0pos : 0 < q0 := (principalIndex_spec H m hm).1
  have hq0H : q0 * m ∈ H := (principalIndex_spec H m hm).2
  ext z
  constructor
  · rintro ⟨ell, hellpos, hzH, hzret⟩
    let r := ell % q0
    by_cases hr0 : r = 0
    · right
      change z - (q0 * m : ℕ) ∈ H.asRelativeIdeal
      change z - (ell * m : ℕ) ∈ H.asRelativeIdeal at hzret
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hzret ⊢
      obtain ⟨y, hyH, hy⟩ := hzret
      have hqdiv : q0 ∣ ell := Nat.dvd_iff_mod_eq_zero.2 hr0
      obtain ⟨k, rfl⟩ := hqdiv
      have hkpos : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        subst k
        simp at hellpos
      refine ⟨y + (k - 1) * (q0 * m),
        H.add_mem hyH (H.toAddSubmonoid.nsmul_mem hq0H (k - 1)), ?_⟩
      have hk : k = (k - 1) + 1 := by omega
      have hy' : z = (y : ℤ) + (q0 * k * m : ℕ) := by
        push_cast at hy ⊢
        omega
      have hdiff : q0 * k * m = q0 * m + (k - 1) * (q0 * m) := by
        calc
          q0 * k * m = q0 * ((k - 1) + 1) * m := by rw [← hk]
          _ = q0 * m + (k - 1) * (q0 * m) := by ring
      rw [hy', hdiff]
      push_cast
      ring
    · left
      refine ⟨r, Nat.pos_of_ne_zero hr0, Nat.mod_lt ell hq0pos, hzH, ?_⟩
      change z - (r * m : ℕ) ∈ H.asRelativeIdeal
      change z - (ell * m : ℕ) ∈ H.asRelativeIdeal at hzret
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hzret ⊢
      obtain ⟨y, hyH, hy⟩ := hzret
      have hell : ell = ell / q0 * q0 + r := by
        calc
          ell = r + q0 * (ell / q0) := by
            simpa [r] using (Nat.mod_add_div ell q0).symm
          _ = ell / q0 * q0 + r := by ring
      refine ⟨y + (ell / q0) * (q0 * m),
        H.add_mem hyH (H.toAddSubmonoid.nsmul_mem hq0H (ell / q0)), ?_⟩
      have hy' : z = (y : ℤ) + (ell * m : ℕ) := by
        push_cast at hy ⊢
        omega
      have hdiff : ell * m = r * m + (ell / q0) * (q0 * m) := by
        calc
          ell * m = (ell / q0 * q0 + r) * m := by rw [← hell]
          _ = r * m + (ell / q0) * (q0 * m) := by ring
      rw [hy', hdiff]
      push_cast
      ring
  · intro hz
    rcases hz with hzprefix | hzprincipal
    · obtain ⟨ell, hellpos, -, hzJ⟩ := hzprefix
      exact ⟨ell, hellpos, hzJ⟩
    · refine ⟨q0, hq0pos, ?_⟩
      refine ⟨?_, hzprincipal⟩
      change z - (q0 * m : ℕ) ∈ H.asRelativeIdeal at hzprincipal
      obtain ⟨y, hyH, hy⟩ :=
        (NumericalSemigroup.mem_asRelativeIdeal_iff H (z - (q0 * m : ℕ))).1 hzprincipal
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨q0 * m + y, H.add_mem hq0H hyH, ?_⟩
      push_cast at hy ⊢
      omega

/-! ### Actual frozen chosen-base normalization -/

abbrev normalizedH (B : Data Gamma) : NumericalSemigroup :=
  normalizedSemigroup (B.tailDegrees 0).val (B.tailDegrees 1).val
    (B.tailDegrees 2).val (B.degrees_positive 1)

abbrev normalizedI (B : Data Gamma) : RelativeIdeal (normalizedH B) :=
  normalizedTailIdeal Gamma B.q.val (B.tailDegrees 0).val
    (B.tailDegrees 1).val (B.tailDegrees 2).val (L5A2B2.chosenBase_minimalFour B)

abbrev normalizedA (B : Data Gamma) : ℕ :=
  (B.tailDegrees 0).val /
    tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val

abbrev normalizedB (B : Data Gamma) : ℕ :=
  (B.tailDegrees 1).val /
    tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val

abbrev normalizedC (B : Data Gamma) : ℕ :=
  (B.tailDegrees 2).val /
    tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val

/-- The paper's normalized return parameter is the actual chosen pivot. -/
abbrev normalizedM (B : Data Gamma) : ℕ := B.q.val

theorem normalized_minimalThree (B : Data Gamma) :
    (normalizedH B).IsMinimallyGeneratedByThree
      (normalizedA B) (normalizedB B) (normalizedC B) :=
  normalizedSemigroup_minimal (L5A2B2.chosenBase_minimalFour B)

/-- In a numerical semigroup presentation, the pivot is coprime to the gcd
of the other three generators.  This is the arithmetic input that turns an
ambient return by `m` into an integral return level after gcd normalization. -/
theorem tailGcd_coprime_pivot {m n₁ n₂ n₃ : ℕ}
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    Nat.Coprime (tailGcd n₁ n₂ n₃) m := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd (tailGcd n₁ n₂ n₃) m
  have hgd : g ∣ tailGcd n₁ n₂ n₃ := Nat.gcd_dvd_left _ _
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  obtain ⟨hd₁, hd₂, hd₃⟩ := tailGcd_dvd n₁ n₂ n₃
  have hall : ∀ x : ℕ, x ∈ Gamma → g ∣ x := by
    intro x hx
    have hx4 : x ∈ generatedFour m n₁ n₂ n₃ := by
      rw [← h.generated]
      exact hx
    obtain ⟨q, y, hy, rfl⟩ := generatedFour_isGeneratedOver m n₁ n₂ n₃ x hx4
    rw [mem_generatedThree_iff] at hy
    obtain ⟨p, r, s, rfl⟩ := hy
    exact dvd_add (dvd_mul_of_dvd_right hgm q)
      (dvd_add (dvd_add (dvd_mul_of_dvd_right (dvd_trans hgd hd₁) p)
        (dvd_mul_of_dvd_right (dvd_trans hgd hd₂) r))
        (dvd_mul_of_dvd_right (dvd_trans hgd hd₃) s))
  obtain ⟨c, hc⟩ := Gamma.exists_conductor
  have hgc := hall c (hc c (le_refl c))
  have hgcsucc := hall (c + 1) (hc (c + 1) (by omega))
  have hcop : Nat.Coprime c (c + 1) := by
    rw [Nat.coprime_self_add_right]
    simp
  change g = 1
  apply Nat.eq_one_of_dvd_one
  rw [← hcop.gcd_eq_one]
  exact Nat.dvd_gcd hgc hgcsucc

/-- A gcd-normalized Apéry-tail element is exactly an element returning to
the normalized semigroup after a positive integral multiple of the original
pivot.  Integrality of the return level is derived from coprimality; it is
not an input to the theorem. -/
theorem mem_normalizedTailIdeal_iff_positive_return
    {m n₁ n₂ n₃ : ℕ}
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) (z : ℤ) :
    z ∈ normalizedTailIdeal Gamma m n₁ n₂ n₃ h ↔
      ∃ ell : ℕ, 0 < ell ∧
        z ∈ returnIdeal (normalizedSemigroup n₁ n₂ n₃ h.n₁_pos) (ell * m) := by
  let d := tailGcd n₁ n₂ n₃
  let Hbar := normalizedSemigroup n₁ n₂ n₃ h.n₁_pos
  have hdpos : 0 < d := tailGcd_pos h.n₁_pos
  constructor
  · intro hz
    change z ∈ (buildTailScaling Gamma m n₁ n₂ n₃ h).ideal at hz
    obtain ⟨x, hxTail, hzx⟩ := hz
    obtain ⟨hdxTail, hmle, hsubGamma⟩ := hxTail
    change d * x ∈ generatedThree n₁ n₂ n₃ at hdxTail
    change m ≤ d * x at hmle
    change d * x - m ∈ Gamma.toAddSubmonoid at hsubGamma
    have hxHbar : x ∈ Hbar := by
      exact ((buildTailScaling Gamma m n₁ n₂ n₃ h).mul_mem_iff x).mp hdxTail
    have hsubFour : d * x - m ∈ generatedFour m n₁ n₂ n₃ := by
      rw [← h.generated]
      exact hsubGamma
    obtain ⟨q, h0, hh0Tail, hdecomp⟩ :=
      generatedFour_isGeneratedOver m n₁ n₂ n₃ (d * x - m) hsubFour
    obtain ⟨y, hyHbar, hh0⟩ :=
      (normalizedSemigroup_scale n₁ n₂ n₃ h.n₁_pos h0).mp hh0Tail
    change h0 = d * y at hh0
    have hmain : d * x = (q + 1) * m + d * y := by
      rw [hh0] at hdecomp
      calc
        d * x = (d * x - m) + m := (Nat.sub_add_cancel hmle).symm
        _ = (q * m + d * y) + m := by rw [hdecomp]
        _ = (q + 1) * m + d * y := by ring
    have hdqm : d ∣ (q + 1) * m := by
      have hdy_le : d * y ≤ d * x := by omega
      have hyx : y ≤ x := Nat.le_of_mul_le_mul_left hdy_le hdpos
      refine ⟨x - y, ?_⟩
      rw [Nat.mul_sub]
      omega
    have hdq : d ∣ q + 1 :=
      (tailGcd_coprime_pivot h).dvd_of_dvd_mul_right hdqm
    obtain ⟨ell, hqell⟩ := hdq
    have hellpos : 0 < ell := by
      by_contra hn
      have hell0 : ell = 0 := Nat.eq_zero_of_not_pos hn
      subst ell
      simp at hqell
    have hxy : x = ell * m + y := by
      apply Nat.eq_of_mul_eq_mul_left hdpos
      calc
        d * x = (q + 1) * m + d * y := hmain
        _ = d * (ell * m + y) := by rw [hqell]; ring
    refine ⟨ell, hellpos, ?_⟩
    change z ∈ Hbar.asRelativeIdeal ∧ z - (ell * m : ℕ) ∈ Hbar.asRelativeIdeal
    constructor
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      exact ⟨x, hxHbar, hzx⟩
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨y, hyHbar, ?_⟩
      rw [hzx]
      have hxyZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hxy
      push_cast at hxyZ ⊢
      omega
  · rintro ⟨ell, hellpos, hzHbar, hzReturn⟩
    change z - (ell * m : ℕ) ∈ Hbar.asRelativeIdeal at hzReturn
    rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hzHbar hzReturn
    obtain ⟨x, hxHbar, hzx⟩ := hzHbar
    obtain ⟨y, hyHbar, hzy⟩ := hzReturn
    have hxy : x = ell * m + y := by
      push_cast at hzx hzy
      omega
    have hdxTail : d * x ∈ generatedThree n₁ n₂ n₃ := by
      exact (normalizedSemigroup_scale n₁ n₂ n₃ h.n₁_pos (d * x)).mpr
        ⟨x, hxHbar, rfl⟩
    have hdyTail : d * y ∈ generatedThree n₁ n₂ n₃ := by
      exact (normalizedSemigroup_scale n₁ n₂ n₃ h.n₁_pos (d * y)).mpr
        ⟨y, hyHbar, rfl⟩
    have hdell : 1 ≤ d * ell := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt hdpos) (Nat.ne_of_gt hellpos))
    have hmle : m ≤ d * x := by
      have hbase : m ≤ (d * ell) * m := by
        simpa using Nat.mul_le_mul_right m hdell
      rw [hxy]
      nlinarith
    have hmGamma : m ∈ Gamma := by
      change m ∈ Gamma.toAddSubmonoid
      rw [h.generated]
      exact firstGenerator_mem_generatedFour m n₁ n₂ n₃
    have hdyGamma : d * y ∈ Gamma := by
      change d * y ∈ Gamma.toAddSubmonoid
      rw [h.generated]
      exact generatedThree_le_generatedFour m n₁ n₂ n₃ hdyTail
    have hsumGamma : (d * ell - 1) * m + d * y ∈ Gamma := by
      exact Gamma.toAddSubmonoid.add_mem
        (by simpa [nsmul_eq_mul] using
          Gamma.toAddSubmonoid.nsmul_mem hmGamma (d * ell - 1))
        hdyGamma
    have hsplit : d * ell * m = (d * ell - 1) * m + m := by
      calc
        d * ell * m = ((d * ell - 1) + 1) * m := by
          rw [Nat.sub_add_cancel hdell]
        _ = (d * ell - 1) * m + m := by ring
    have hdx : d * x = m + ((d * ell - 1) * m + d * y) := by
      calc
        d * x = d * (ell * m + y) := by rw [hxy]
        _ = d * ell * m + d * y := by ring
        _ = ((d * ell - 1) * m + m) + d * y := by rw [hsplit]
        _ = m + ((d * ell - 1) * m + d * y) := by ring
    have hsubGamma : d * x - m ∈ Gamma := by
      have hsubeq : d * x - m = (d * ell - 1) * m + d * y := by omega
      rw [hsubeq]
      exact hsumGamma
    apply (mem_normalizedTailIdeal_iff Gamma m n₁ n₂ n₃ h z).2
    refine ⟨d * x, ⟨hdxTail, hmle, hsubGamma⟩, ?_⟩
    rw [hzx]
    push_cast
    rfl

abbrev actualPrincipalIndex (B : Data Gamma) : ℕ :=
  principalIndex (normalizedH B) (normalizedM B) B.q_positive

theorem actualPrincipalIndex_spec (B : Data Gamma) :
    0 < actualPrincipalIndex B ∧
      actualPrincipalIndex B * normalizedM B ∈ normalizedH B :=
  principalIndex_spec (normalizedH B) (normalizedM B) B.q_positive

abbrev actualPrefixCarrier (B : Data Gamma) : Set ℤ :=
  prefixCarrier (normalizedH B) (normalizedM B) (actualPrincipalIndex B)

abbrev actualFinalCarrier (B : Data Gamma) : Set ℤ :=
  finalCarrier (normalizedH B) (normalizedM B) (actualPrincipalIndex B)

/-- The frozen chosen-base normalized tail is the union of its positive
return ideals, with the return parameter equal to the actual pivot. -/
theorem mem_normalizedTailIdeal_iff_actualPositiveReturn
    (B : Data Gamma) (z : ℤ) :
    z ∈ normalizedI B ↔
      z ∈ positiveReturnCarrier (normalizedH B) (normalizedM B) := by
  exact mem_normalizedTailIdeal_iff_positive_return
    (L5A2B2.chosenBase_minimalFour B) z

/-- The actual normalized Apéry-tail carrier is exactly the source-complete
prefix carrier with its first principal return inserted. -/
theorem normalizedTailIdeal_eq_actualFinalCarrier (B : Data Gamma) :
    (normalizedI B).carrier = actualFinalCarrier B := by
  calc
    (normalizedI B).carrier =
        positiveReturnCarrier (normalizedH B) (normalizedM B) := by
      ext z
      exact mem_normalizedTailIdeal_iff_actualPositiveReturn B z
    _ = finalCarrier (normalizedH B) (normalizedM B)
        (principalIndex (normalizedH B) (normalizedM B) B.q_positive) :=
      positiveReturnCarrier_eq_finalCarrier
        (normalizedH B) (normalizedM B) B.q_positive
    _ = actualFinalCarrier B := rfl

/-- Actual Sector-B specialization of M1.  No Gate/RECORD datum, coordinate,
family tag, or additional Sector-B assumption is smuggled into the statement. -/
theorem sectorB_branchBirth_isPrefixSource (P : L5A1.P2Data Gamma)
    (_hB : L5A1.SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    IsSource (normalizedH P.M.base) (actualPrefixCarrier P.M.base) s :=
  branchBirth_isPrefixSource hs

/-- Canonical nonprincipal return level attached to an actual Sector-B
BRANCH-BIRTH source. -/
def sectorBCanonicalReturnIndex (P : L5A1.P2Data Gamma)
    (hB : L5A1.SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) : ℕ :=
  canonicalReturnIndex (sectorB_branchBirth_isPrefixSource P hB hs)

theorem sectorBCanonicalReturnIndex_spec (P : L5A1.P2Data Gamma)
    (hB : L5A1.SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    ReturnWitness (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s (sectorBCanonicalReturnIndex P hB hs) :=
  canonicalReturnIndex_spec (sectorB_branchBirth_isPrefixSource P hB hs)

end NS25Lean.L5A2B4AR1
