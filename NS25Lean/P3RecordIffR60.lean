import NS25Lean.P3RecordGeometryR60
import NS25Lean.P3RecordArithmeticR60
import NS25Lean.P3PrefixRoutingR60

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R60
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4I L5A2C4OR3 L5A2C4OR4 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

def returnDefectNat (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℕ :=
  (returnDefect B e q).toNat

def recordCeiling (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℕ :=
  runningMinimum (criticalExponent M.base (e 0)) (returnDefectNat M.base e) (q-1)

def recordHeight (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℕ :=
  recordCeiling M e q-returnDefectNat M.base e q

def StrictRecord (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : Prop :=
  returnDefectNat M.base e q < criticalExponent M.base (e 0) ∧
    ∀ r : ℕ, 0 < r → r < q → returnDefectNat M.base e q < returnDefectNat M.base e r

def recordSeed (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ZMod (routingA B e) :=
  ((returnPoint B e q-routingB B e-routingC B e : ℤ) : ZMod (routingA B e))

def birthData (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q) :
    CombinatorialCore.ResidueData (ZMod (routingA B e)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact idealData (birthIdeal (routingH B e) B.q.val q hq)
    (routingA B e) (routingB B e) (routingC B e) (routingHB B e) (routingHC B e)

theorem routingA_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingA B e ∈ routingH B e := by
  change _ ∈ generatedThree _ _ _
  exact AddSubmonoid.subset_closure (by simp)

theorem canonical_shift_mem_iff (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ℤ) (hx : CanonicalValue B e x) (n : ℤ) :
    x+(routingA B e : ℤ)*n ∈ (routingH B e).asRelativeIdeal ↔ 0 ≤ n := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact semigroup_apery_shift_mem_iff (routingH B e) (routingA B e)
    (routingA_mem B e) x hx n

theorem nonprincipal_defectNat_cast (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    (returnDefectNat M.base e q : ℤ) = returnDefect M.base e q :=
  Int.toNat_of_nonneg (nonprincipal_canonical_stencil M hp e hlive q hq hpre).1.le

/-- Exact membership at any one of the three canonical predecessor cells.
Earlier return p is evaluated at the difference index q-p, not at beta_p. -/
theorem prefix_stencil_shift_mem_iff (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (w : ℤ)
    (hcan : ∀ r : ℕ, 0 < r → r ≤ q →
      CanonicalValue M.base e (returnPoint M.base e r-w))
    (hgate : CanonicalValue M.base e
      ((criticalExponent M.base (e 0) : ℤ)*routingA M.base e-w)) (n : ℕ) :
    returnPoint M.base e q-w+(routingA M.base e : ℤ)*n ∈
      birthIdeal (routingH M.base e) M.base.q.val q hq ↔
      recordCeiling M e q ≤ returnDefectNat M.base e q+n := by
  let x := returnPoint M.base e q-w
  let C := criticalExponent M.base (e 0)
  let d := returnDefectNat M.base e
  have hdq : (d q : ℤ) = returnDefect M.base e q :=
    nonprincipal_defectNat_cast M hp e hlive q hq hpre
  have hxH : x+(routingA M.base e : ℤ)*n ∈ (routingH M.base e).asRelativeIdeal :=
    (canonical_shift_mem_iff M.base e x (hcan q hq le_rfl) n).2 (by positivity)
  have hret (p : ℕ) (hp0 : 0 < p) (hpq : p ≤ q) :
      x+(routingA M.base e : ℤ)*n ∈ returnIdeal (routingH M.base e) (p*M.base.q.val) ↔
        (if p=q then C else d (q-p)) ≤ d q+n := by
    rw [mem_returnIdeal_iff]
    simp only [hxH, true_and]
    by_cases he : p=q
    · subst p
      rw [if_pos rfl]
      have hEq : x+(routingA M.base e : ℤ)*n-(q*M.base.q.val : ℕ) =
          ((C : ℤ)*routingA M.base e-w)+
            (routingA M.base e : ℤ)*((d q : ℤ)+n-C) := by
        dsimp only [x]
        rw [return_point_defect_eq, ← hdq]
        simp only [Nat.cast_mul]
        ring
      rw [hEq, canonical_shift_mem_iff M.base e _ hgate]
      omega
    · rw [if_neg he]
      let r := q-p
      have hr : 0 < r := by dsimp [r]; omega
      have hrq : r ≤ q := Nat.sub_le _ _
      have hrpre : r < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by omega
      have hdr : (d r : ℤ) = returnDefect M.base e r :=
        nonprincipal_defectNat_cast M hp e hlive r hr hrpre
      have hqr : (q : ℤ) = p+r := by exact_mod_cast (show q=p+r by dsimp [r]; omega)
      have hEq : x+(routingA M.base e : ℤ)*n-(p*M.base.q.val : ℕ) =
          (returnPoint M.base e r-w)+
            (routingA M.base e : ℤ)*((d q : ℤ)+n-d r) := by
        dsimp only [x]
        rw [return_point_defect_eq M.base e q, return_point_defect_eq M.base e r,
          ← hdq, ← hdr]
        simp only [Nat.cast_mul]
        rw [hqr]
        ring
      rw [hEq, canonical_shift_mem_iff M.base e _ (hcan r hr hrq)]
      change 0 ≤ (d q : ℤ)+n-d r ↔ d r ≤ d q+n
      omega
  change (∃ p : ℕ, 0 < p ∧ p < q+1 ∧
    x+(routingA M.base e : ℤ)*n ∈ returnIdeal (routingH M.base e) (p*M.base.q.val)) ↔
      runningMinimum C d (q-1) ≤ d q+n
  rw [runningMinimum_le_iff]
  constructor
  · rintro ⟨p,hp0,hpq,hm⟩
    have hh := (hret p hp0 (by omega)).1 hm
    by_cases he : p=q
    · exact Or.inl (by simpa [he] using hh)
    · exact Or.inr ⟨q-p, by omega, by omega, by simpa only [if_neg he] using hh⟩
  · rintro (hC | ⟨r,hr0,hrq,hdr⟩)
    · exact ⟨q,hq,by omega,(hret q hq le_rfl).2 (by simpa using hC)⟩
    · have hp0 : 0 < q-r := by omega
      have hpq : q-r ≤ q := Nat.sub_le _ _
      have hne : q-r ≠ q := by omega
      have hsub : q-(q-r)=r := by omega
      refine ⟨q-r,hp0,by omega,(hret (q-r) hp0 hpq).2 ?_⟩
      simpa only [if_neg hne, hsub] using hdr

theorem prefix_stencil_representative (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (w : ℤ)
    (hcan : ∀ r : ℕ, 0 < r → r ≤ q →
      CanonicalValue M.base e (returnPoint M.base e r-w))
    (hgate : CanonicalValue M.base e
      ((criticalExponent M.base (e 0) : ℤ)*routingA M.base e-w)) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    (birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
      (routingA M.base e) ((returnPoint M.base e q-w : ℤ) : ZMod (routingA M.base e)) =
      returnPoint M.base e q-w+(routingA M.base e : ℤ)*recordHeight M e q := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let I := birthIdeal (routingH M.base e) M.base.q.val q hq
  let x := returnPoint M.base e q-w
  let k := recordHeight M e q
  have hdiff : k = recordCeiling M e q-returnDefectNat M.base e q := rfl
  have hmem : x+(routingA M.base e : ℤ)*k ∈ I :=
    (prefix_stencil_shift_mem_iff M hp e hlive q hq hpre w hcan hgate k).2 (by omega)
  have hprev : x+(routingA M.base e : ℤ)*k-routingA M.base e ∉ I := by
    intro hm
    by_cases hk : k=0
    · obtain ⟨p,hp0,hpq,hmH,_⟩ := hm
      have hh : x+(routingA M.base e : ℤ)*(-1) ∈ (routingH M.base e).asRelativeIdeal := by
        convert hmH using 1 <;> simp only [hk, Nat.cast_zero, mul_zero, add_zero] <;> ring
      have := (canonical_shift_mem_iff M.base e x (hcan q hq le_rfl) (-1)).1 hh
      omega
    · have he : x+(routingA M.base e : ℤ)*k-routingA M.base e =
          x+(routingA M.base e : ℤ)*(k-1 : ℕ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num only [Nat.cast_one]; ring
      rw [he] at hm
      have hh := (prefix_stencil_shift_mem_iff M hp e hlive q hq hpre w hcan hgate (k-1)).1 hm
      omega
  have hh := aperyRepresentative_eq_of_mem_not_mem_sub I (routingA M.base e)
    (routingA_mem M.base e) _ hmem hprev
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero] using hh

theorem birth_target_representative (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    (birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
      (routingA M.base e) (returnPoint M.base e q : ZMod (routingA M.base e)) =
      returnPoint M.base e q := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let I := birthIdeal (routingH M.base e) M.base.q.val q hq
  let beta := returnPoint M.base e q
  have hcan := (nonprincipal_canonical_stencil M hp e hlive q hq hpre).2.2.1
  have hbH : beta ∈ (routingH M.base e).asRelativeIdeal := by
    simpa only [mul_zero, add_zero] using
      (canonical_shift_mem_iff M.base e beta hcan 0).2 (by omega)
  have hdq := nonprincipal_defectNat_cast M hp e hlive q hq hpre
  have htail : (routingA M.base e*returnDefectNat M.base e q : ℕ) ∈ routingH M.base e := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (routingH M.base e).toAddSubmonoid.nsmul_mem (routingA_mem M.base e) (returnDefectNat M.base e q)
  have hret : beta-(q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal := by
    have he : beta-(q*M.base.q.val : ℕ) =
        (routingA M.base e*returnDefectNat M.base e q : ℕ) := by
      dsimp only [beta]
      rw [return_point_defect_eq, ← hdq]
      simp only [Nat.cast_mul]
      ring
    rw [he]
    exact ⟨_,htail,rfl⟩
  have hmem : beta ∈ I := ⟨q,hq,by omega,hbH,hret⟩
  have hprev : beta-routingA M.base e ∉ I := by
    rintro ⟨p,hp0,hpq,hmH,_⟩
    have hh : beta+(routingA M.base e : ℤ)*(-1) ∈ (routingH M.base e).asRelativeIdeal := by
      convert hmH using 1 <;> ring
    have := (canonical_shift_mem_iff M.base e beta hcan (-1)).1 hh
    omega
  exact aperyRepresentative_eq_of_mem_not_mem_sub I (routingA M.base e)
    (routingA_mem M.base e) beta hmem hprev

/-- G2's genuine four representatives, in the actual ideal after inserting level q. -/
theorem birth_apery_stencil (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let I := birthIdeal (routingH M.base e) M.base.q.val q hq
    let x := returnPoint M.base e q-routingB M.base e-routingC M.base e
    let a := routingA M.base e
    let k := recordHeight M e q
    I.aperyRepresentative a (x : ZMod a) = x+a*k ∧
    I.aperyRepresentative a ((x+routingB M.base e : ℤ) : ZMod a) = x+routingB M.base e+a*k ∧
    I.aperyRepresentative a ((x+routingC M.base e : ℤ) : ZMod a) = x+routingC M.base e+a*k ∧
    I.aperyRepresentative a ((x+routingB M.base e+routingC M.base e : ℤ) : ZMod a) =
      x+routingB M.base e+routingC M.base e := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let x := returnPoint M.base e q-routingB M.base e-routingC M.base e
  have hcan (r : ℕ) (hr : 0 < r) (hrq : r ≤ q) :=
    nonprincipal_canonical_stencil M hp e hlive r hr (by omega)
  have hg := gate_canonical_stencil M hp e
  have hbc := prefix_stencil_representative M hp e hlive q hq hpre
    ((routingB M.base e : ℤ)+routingC M.base e)
    (by intro r hr hrq; simpa only [sub_add_eq_sub_sub] using (hcan r hr hrq).2.2.2.2.2)
    (by simpa only [sub_add_eq_sub_sub] using hg.2.2)
  have hb := prefix_stencil_representative M hp e hlive q hq hpre (routingB M.base e)
    (by intro r hr hrq; exact (hcan r hr hrq).2.2.2.1) hg.1
  have hc := prefix_stencil_representative M hp e hlive q hq hpre (routingC M.base e)
    (by intro r hr hrq; exact (hcan r hr hrq).2.2.2.2.1) hg.2.1
  have ht := birth_target_representative M hp e hlive q hq hpre
  have heB : x+routingB M.base e=returnPoint M.base e q-routingC M.base e := by dsimp [x]; ring
  have heC : x+routingC M.base e=returnPoint M.base e q-routingB M.base e := by dsimp [x]; ring
  have heT : x+routingB M.base e+routingC M.base e=returnPoint M.base e q := by dsimp [x]; ring
  exact ⟨by simpa only [sub_add_eq_sub_sub] using hbc, by rw [heB]; exact hc,
    by rw [heC]; exact hb, by rw [heT]; exact ht⟩

theorem birth_sourceTargetBranch_iff_record (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    ResidueData.SourceTargetBranch (birthData M.base e q hq) (recordSeed M.base e q) ↔
      StrictRecord M e q := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨h0,hb,hc,ht⟩ := birth_apery_stencil M hp e hlive q hq hpre
  have hi := sourceTargetBranch_iff_of_stencil
    (birthIdeal (routingH M.base e) M.base.q.val q hq)
    (routingA M.base e) (routingB M.base e) (routingC M.base e)
    (routingHB M.base e) (routingHC M.base e)
    (returnPoint M.base e q-routingB M.base e-routingC M.base e)
    (recordHeight M e q) h0 hb hc ht
  exact hi.trans (record_height_pos_iff _ _ q hq)

/-- Original R2 binder, retaining the actual physical legal witness and G1.
The graph in G2 is the real birth prefix, not the final principal-inserted graph. -/
theorem r2_record_iff_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card=2) :
    ∃ e : Fin 3 ≃ Fin 3,
      killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1 ∧
      (∀ i : Fin 3, i≠2 → ∀ k : Fin 3,
        criticalExponent M.base (e i)*weights M.base (e i)-weights M.base k ∈ M.base.apery) ∧
      P3R59.OneArmPrefix M hp e ∧
      ∀ q : ℕ, ∀ hq : 0 < q,
        q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
        (ResidueData.SourceTargetBranch (birthData M.base e q hq) (recordSeed M.base e q) ↔
          StrictRecord M e q) := by
  obtain ⟨e,hboundary,hlive⟩ := P3R57.r2_legal_boundary_role M hp hR2
  refine ⟨e,hboundary,hlive,P3R59.oneArmPrefix_of_legal_role M hp e hboundary
    (hlive 0 (by decide)),?_⟩
  intro q hq hpre
  exact birth_sourceTargetBranch_iff_record M hp e (hlive 0 (by decide)) q hq hpre

theorem birth_branch_target (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (hq : 0 < q) :
    (birthData B e q hq).branchTarget (recordSeed B e q) =
      (returnPoint B e q : ZMod (routingA B e)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hh := idealData_branchTarget (birthIdeal (routingH B e) B.q.val q hq)
    (routingA B e) (routingB B e) (routingC B e) (routingHB B e) (routingHC B e)
    (returnPoint B e q-routingB B e-routingC B e)
  change (birthData B e q hq).branchTarget (recordSeed B e q) = _ at hh
  have he : returnPoint B e q-routingB B e-routingC B e+routingB B e+routingC B e =
      returnPoint B e q := by ring
  rw [he] at hh
  exact hh

theorem strictRecord_iff_signed (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    StrictRecord M e q ↔
      returnDefect M.base e q < criticalExponent M.base (e 0) ∧
      ∀ r : ℕ, 0 < r → r < q → returnDefect M.base e q < returnDefect M.base e r := by
  have hdq := nonprincipal_defectNat_cast M hp e hlive q hq hpre
  constructor
  · rintro ⟨hC,hr⟩
    refine ⟨by rw [← hdq]; exact_mod_cast hC, ?_⟩
    intro r hr0 hrq
    have hdr := nonprincipal_defectNat_cast M hp e hlive r hr0 (by omega)
    rw [← hdq, ← hdr]
    exact_mod_cast hr r hr0 hrq
  · rintro ⟨hC,hr⟩
    refine ⟨by rw [← hdq] at hC; exact_mod_cast hC, ?_⟩
    intro r hr0 hrq
    have hdr := nonprincipal_defectNat_cast M hp e hlive r hr0 (by omega)
    have hh := hr r hr0 hrq
    rw [← hdq, ← hdr] at hh
    exact_mod_cast hh

end NS25Lean.P3R60
