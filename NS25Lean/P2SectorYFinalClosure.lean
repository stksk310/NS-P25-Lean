import NS25Lean.P2SectorYPureFiberPivot
import NS25Lean.StaircaseCornerBound
import NS25Lean.AppendixASourceOrder

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1

open ChosenBase FourGeneratedBridge Presentation MvPolynomial

variable {Gamma : NumericalSemigroup}

theorem monomial_mem_chosen_iff_boundary (k : Type*) [Field k]
    (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    monomial u (1 : k) ∈ B.J k ↔ L2B.weight B u ∈ B.K := by
  rw [B.J_eq_comap_tail k]
  change ToricPresentation.toricMap k B.H B.tailDegrees (monomial u 1) ∈
    ToricPresentation.tailMonomialIdeal k Gamma.toAddSubmonoid B.H B.q.val ↔ _
  rw [B.tailMap_monomial k,
    ToricPresentation.single_mem_tailMonomialIdeal_iff k _ _ _ B.H_le]
  rw [← L2B.weight_eq_degree]
  rfl

theorem standard_iff_chosen_apery (k : Type*) [Field k]
    (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    u ∈ L3A.standardExponents (B.J k) ↔ L2B.weight B u ∈ B.apery := by
  rw [B.apery_eq_compl]
  change monomial u (1 : k) ∉ B.J k ↔
    L2B.weight B u ∈ B.H ∧ L2B.weight B u ∉ B.K
  rw [monomial_mem_chosen_iff_boundary]
  simp only [L3C.weight_mem_H, true_and]

theorem apery_mod_unique (B : Data Gamma) {d e : ℕ}
    (hd : d ∈ B.apery) (he : e ∈ B.apery)
    (hmod : Nat.ModEq B.q.val d e) : d = e := by
  have forward {d e : ℕ} (hd : d ∈ B.apery) (he : e ∈ B.apery)
      (hmod : Nat.ModEq B.q.val d e) (hde : d ≤ e) : d = e := by
    have hdiv : B.q.val ∣ e - d := (Nat.modEq_iff_dvd' hde).mp hmod
    obtain ⟨c, hc⟩ := hdiv
    by_cases hc0 : c = 0
    · subst c
      simp only [mul_zero] at hc
      omega
    have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
    have hcstep : c = (c - 1) + 1 := by omega
    have heq0 : e = d + B.q.val * c := by omega
    rw [hcstep, Nat.mul_add] at heq0
    have hqGamma : B.q.val ∈ Gamma := B.q.property
    have hdGamma : d ∈ Gamma := hd.1
    have hsubGamma : e - B.q.val ∈ Gamma := by
      have heq : e - B.q.val = d + (c - 1) * B.q.val := by
        rw [Nat.mul_comm (c - 1) B.q.val]
        omega
      rw [heq]
      exact Gamma.toAddSubmonoid.add_mem hdGamma
        (Gamma.toAddSubmonoid.nsmul_mem hqGamma (c - 1))
    rcases he.2 with hlt | hn
    · have hqpos := B.q_positive
      omega
    · exact (hn hsubGamma).elim
  rcases le_total d e with hde | hed
  · exact forward hd he hmod hde
  · exact (forward he hd hmod.symm hed).symm

theorem standard_residue_unique (k : Type*) [Field k]
    (B : Data Gamma) (hz : L2C.internalLoad B B.pivot = 0)
    {u v : Fin 3 →₀ ℕ}
    (hu : u ∈ L3A.standardExponents (B.J k))
    (hv : v ∈ L3A.standardExponents (B.J k))
    (hmod : Nat.ModEq B.q.val (L2B.weight B u) (L2B.weight B v)) : u = v := by
  have hua := (standard_iff_chosen_apery k B u).mp hu
  have hva := (standard_iff_chosen_apery k B v).mp hv
  have hw : L2B.weight B u = L2B.weight B v := apery_mod_unique B hua hva hmod
  exact L2C.apery_tail_unique B hz u v hw hua

theorem exists_apery_same_residue (B : Data Gamma) (x : ℕ) (hx : x ∈ Gamma) :
    ∃ d : ℕ, d ∈ B.apery ∧ Nat.ModEq B.q.val x d := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases ha : x ∈ B.apery
      · exact ⟨x, ha, .rfl⟩
      · have hxq : B.q.val ≤ x := by
          by_contra hn
          apply ha
          exact ⟨hx, Or.inl (by omega)⟩
        have hxsub : x - B.q.val ∈ Gamma := by
          by_contra hn
          apply ha
          exact ⟨hx, Or.inr hn⟩
        have hlt : x - B.q.val < x := by
          have := B.q_positive
          omega
        obtain ⟨d, hd, hmod⟩ := ih (x - B.q.val) hlt hxsub
        refine ⟨d, hd, ?_⟩
        exact (Nat.sub_modulus_modEq_iff hxq).mp hmod

theorem exists_standard_same_residue (k : Type*) [Field k]
    (B : Data Gamma) (a : Fin 3 →₀ ℕ) :
    ∃ v : Fin 3 →₀ ℕ,
      v ∈ L3A.standardExponents (B.J k) ∧
      Nat.ModEq B.q.val (L2B.weight B a) (L2B.weight B v) := by
  have hx : L2B.weight B a ∈ Gamma := B.H_le (L3C.weight_mem_H B a)
  obtain ⟨d, hd, hmod⟩ := exists_apery_same_residue B _ hx
  obtain ⟨f, hf⟩ := factorizationMap_surjective B.family
    (ToricPresentation.subtype_degrees_generate _ _ B.generates.symm)
    (⟨d, hd.1⟩ : Gamma.toAddSubmonoid)
  let F : L2C.FactorizationFiber B d :=
    ⟨f, (L2C.weight_eq_degree B f).trans (congrArg Subtype.val hf)⟩
  have hp : F.val B.pivot = 0 := L2C.apery_pivot_coordinate_zero B d hd F
  let v : L2B.FactorizationFiber B d :=
    (tailFiberEquivPivotZero B d).symm ⟨F, hp⟩
  refine ⟨v.val, (standard_iff_chosen_apery k B v.val).mpr ?_, ?_⟩
  · simpa only [v.property] using hd
  · simpa only [v.property] using hmod

theorem minimal_predecessor_standard (k : Type*) [Field k]
    (B : Data Gamma) {g : Fin 3 →₀ ℕ}
    (hg : g ∈ L3A.minimalExponents (B.J k)) (i : Fin 3) (hi : 0 < g i) :
    g - Finsupp.single i 1 ∈ L3A.standardExponents (B.J k) := by
  intro hm
  have hle : g - Finsupp.single i 1 ≤ g := tsub_le_self
  have hback := hg.2 hm hle
  have hcoord := hback i
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hcoord
  omega

theorem sectorY_full_support_first_stage (k : Type*) [Field k]
    (B : Data Gamma) (hz : L2C.internalLoad B B.pivot = 0)
    (g : Fin 3 →₀ ℕ) (hg : g ∈ L3A.fullSupportGenerators (B.J k))
    (v : Fin 3 →₀ ℕ) (hv : v ∈ L3A.standardExponents (B.J k))
    (hres : Nat.ModEq B.q.val (L2B.weight B g) (L2B.weight B v)) : v = 0 := by
  by_contra hv0
  obtain ⟨i, hi⟩ : ∃ i, 0 < v i := by
    by_contra hn
    push_neg at hn
    apply hv0
    ext i
    exact Nat.eq_zero_of_le_zero (hn i)
  let e := Finsupp.single i 1
  have heg : e ≤ g := Finsupp.single_le_iff.mpr (hg.2 i)
  have hev : e ≤ v := Finsupp.single_le_iff.mpr hi
  have hgstd := minimal_predecessor_standard k B hg.1 i (hg.2 i)
  have hvstd : v - e ∈ L3A.standardExponents (B.J k) :=
    L3A.Staircase.downward (B.J k) hv tsub_le_self
  have hdecomp_g : L2B.weight B (g - e) + L2B.weight B e = L2B.weight B g := by
    rw [← map_add, tsub_add_cancel_of_le heg]
  have hdecomp_v : L2B.weight B (v - e) + L2B.weight B e = L2B.weight B v := by
    rw [← map_add, tsub_add_cancel_of_le hev]
  have hwg : L2B.weight B e ≤ L2B.weight B g := by omega
  have hwv : L2B.weight B e ≤ L2B.weight B v := by omega
  have hsub : Nat.ModEq B.q.val
      (L2B.weight B g - L2B.weight B e)
      (L2B.weight B v - L2B.weight B e) :=
    Nat.ModEq.sub hwg hwv hres .rfl
  have hweights_g : L2B.weight B (g - e) =
      L2B.weight B g - L2B.weight B e := by
    omega
  have hweights_v : L2B.weight B (v - e) =
      L2B.weight B v - L2B.weight B e := by
    omega
  have heq : g - e = v - e := standard_residue_unique k B hz hgstd hvstd (by
    rw [hweights_g, hweights_v]
    exact hsub)
  have hgv : g = v := by
    have hadd := congrArg (fun x => x + e) heq
    simpa only [tsub_add_cancel_of_le heg, tsub_add_cancel_of_le hev] using hadd
  exact hv (hgv ▸ hg.1.1)

theorem sectorY_full_support_second_stage (k : Type*) [Field k]
    (B : Data Gamma) (hz : L2C.internalLoad B B.pivot = 0)
    (u : Fin 3 →₀ ℕ) (r : Fin 3) (a : ℕ)
    (hupure : u = Finsupp.single r a) (hua : 0 < a)
    (humin : u ∈ L3A.minimalExponents (B.J k))
    (hures : Nat.ModEq B.q.val (L2B.weight B u) 0)
    (g : Fin 3 →₀ ℕ) (hg : g ∈ L3A.fullSupportGenerators (B.J k))
    (hgres : Nat.ModEq B.q.val (L2B.weight B g) 0) : False := by
  let e := Finsupp.single r 1
  have heu : e ≤ u := by
    rw [hupure]
    dsimp [e]
    have ha1 : 1 ≤ a := by omega
    exact Finsupp.single_le_iff.mpr (by simpa using ha1)
  have heg : e ≤ g := Finsupp.single_le_iff.mpr (hg.2 r)
  have hur : 0 < u r := by rw [hupure]; simpa using hua
  have hustd := minimal_predecessor_standard k B humin r hur
  have hgstd := minimal_predecessor_standard k B hg.1 r (hg.2 r)
  have hgu : Nat.ModEq B.q.val (L2B.weight B g) (L2B.weight B u) :=
    hgres.trans hures.symm
  have hdecomp_g : L2B.weight B (g - e) + L2B.weight B e = L2B.weight B g := by
    rw [← map_add, tsub_add_cancel_of_le heg]
  have hdecomp_u : L2B.weight B (u - e) + L2B.weight B e = L2B.weight B u := by
    rw [← map_add, tsub_add_cancel_of_le heu]
  have hwg : L2B.weight B e ≤ L2B.weight B g := by omega
  have hwu : L2B.weight B e ≤ L2B.weight B u := by omega
  have hsub := Nat.ModEq.sub hwg hwu hgu (Nat.ModEq.rfl : Nat.ModEq B.q.val _ _)
  have hweights_g : L2B.weight B (g - e) =
      L2B.weight B g - L2B.weight B e := by
    omega
  have hweights_u : L2B.weight B (u - e) =
      L2B.weight B u - L2B.weight B e := by
    omega
  have heq : g - e = u - e := standard_residue_unique k B hz hgstd hustd (by
    rw [hweights_g, hweights_u]
    exact hsub)
  have hgu_eq : g = u := by
    have hadd := congrArg (fun x => x + e) heq
    simpa only [tsub_add_cancel_of_le heg, tsub_add_cancel_of_le heu] using hadd
  let s : Fin 3 := if r = 0 then 1 else 0
  have hsr : s ≠ r := by
    dsimp [s]
    split_ifs with hr
    · subst r; decide
    · simpa [Ne.symm hr]
  have hzero : u s = 0 := by simp [hupure, Finsupp.single_eq_of_ne hsr]
  have hpos := hg.2 s
  rw [hgu_eq, hzero] at hpos
  omega

theorem repivot_tail_role_exists (B : Data Gamma) {i j : Fin 4} (hji : j ≠ i) :
    ∃ r : Fin 3, (L2C.atPivot B i).order r.succ = j := by
  let Q := L2C.atPivot B i
  have hn : Q.order.symm j ≠ 0 := by
    intro hzero
    have hj : j = Q.order 0 := by
      rw [← hzero, Q.order.apply_symm_apply]
    have hq0 : Q.order 0 = i := by simp [Q, Data.order, L2C.atPivot]
    exact hji (hj.trans hq0)
  obtain ⟨r, hr⟩ := Fin.exists_succ_eq.mpr hn
  refine ⟨r, ?_⟩
  rw [hr, Q.order.apply_symm_apply]

theorem sectorY_repivot_residue_zero_minimal_generator
    (k : Type*) [Field k] (P : P2Data Gamma)
    (pkg : SectorYPureFiberMonomialPivotPackage P) :
    let Q := L2C.atPivot P.M.base (P.M.base.order pkg.q.succ)
    ∃ r : Fin 3, ∃ a : ℕ, ∃ u : Fin 3 →₀ ℕ,
      0 < a ∧ u = Finsupp.single r a ∧
      u ∈ L3A.minimalExponents (Q.J k) ∧
      Nat.ModEq Q.q.val (L2B.weight Q u) 0 := by
  classical
  let B := P.M.base
  let iq := B.order pkg.q.succ
  let ij := B.order pkg.j.succ
  let Q := L2C.atPivot B iq
  have hij : ij ≠ iq := by
    intro h
    exact pkg.q_ne_j (Fin.succ_injective 3 (B.order.injective h.symm))
  obtain ⟨r, hr⟩ := repivot_tail_role_exists B hij
  let a := pkg.jPower.val pkg.j
  let aq := pkg.qPower.val pkg.q
  let u : Fin 3 →₀ ℕ := Finsupp.single r a
  have ha : 0 < a := pkg.jPower_pos
  have haq : 0 < aq := pkg.qPower_pos
  have hjdeg : pkg.L = a * L2B.weights B pkg.j := by
    calc
      pkg.L = L2B.weight B pkg.jPower.val := pkg.jPower.property.symm
      _ = L2B.weight B (Finsupp.single pkg.j a) := congrArg _ pkg.jPower_pure
      _ = a * L2B.weights B pkg.j := L2B.weight_single B pkg.j a
  have hqdeg : pkg.L = aq * L2B.weights B pkg.q := by
    calc
      pkg.L = L2B.weight B pkg.qPower.val := pkg.qPower.property.symm
      _ = L2B.weight B (Finsupp.single pkg.q aq) := congrArg _ pkg.qPower_pure
      _ = aq * L2B.weights B pkg.q := L2B.weight_single B pkg.q aq
  have hwr : L2B.weights Q r = L2B.weights B pkg.j := by
    change (Q.family (Q.order r.succ)).val =
      (B.family (B.order pkg.j.succ)).val
    rw [hr]
    rfl
  have hqval : Q.q.val = L2B.weights B pkg.q := by
    change (B.family iq).val = (B.family (B.order pkg.q.succ)).val
    rfl
  have hwu : L2B.weight Q u = pkg.L := by
    rw [show u = Finsupp.single r a from rfl, L2B.weight_single, hwr, ← hjdeg]
  have hLq : pkg.L = aq * Q.q.val := by rw [hqval]; exact hqdeg
  have huK : L2B.weight Q u ∈ Q.K := by
    rw [hwu]
    refine ⟨hwu ▸ L3C.weight_mem_H Q u, ?_, ?_⟩
    · rw [hLq]
      nlinarith [Q.q_positive]
    · have he : pkg.L - Q.q.val = (aq - 1) * Q.q.val := by
        rw [hLq]
        calc
          aq * Q.q.val - Q.q.val = aq * Q.q.val - 1 * Q.q.val := by simp
          _ = (aq - 1) * Q.q.val := (Nat.sub_mul aq 1 Q.q.val).symm
      rw [he]
      exact Gamma.toAddSubmonoid.nsmul_mem Q.q.property (aq - 1)
  have hpredNotK : L2B.weight Q (u - Finsupp.single r 1) ∉ Q.K := by
    intro hpred
    have her : Finsupp.single r 1 ≤ u := by
      dsimp [u]
      have ha1 : 1 ≤ a := by omega
      exact Finsupp.single_le_iff.mpr (by simpa using ha1)
    have hpredWeight : L2B.weight Q (u - Finsupp.single r 1) =
        pkg.L - L2B.weights B pkg.j := by
      have hdecomp : L2B.weight Q (u - Finsupp.single r 1) +
          L2B.weight Q (Finsupp.single r 1) = L2B.weight Q u := by
        rw [← map_add, tsub_add_cancel_of_le her]
      rw [L2B.weight_single, one_mul, hwr, hwu] at hdecomp
      omega
    have hres : (pkg.L - L2B.weights B pkg.j) - Q.q.val ∈ Gamma := by
      rw [← hpredWeight]
      exact hpred.2.2
    obtain ⟨w, hw⟩ := factorizationMap_surjective B.family
      (ToricPresentation.subtype_degrees_generate _ _ B.generates.symm)
      (⟨(pkg.L - L2B.weights B pkg.j) - Q.q.val, hres⟩ : Gamma.toAddSubmonoid)
    let vexp : Fin 4 →₀ ℕ := w + Finsupp.single iq 1 + Finsupp.single ij 1
    have hwdeg : L2C.weight B w =
        (pkg.L - L2B.weights B pkg.j) - Q.q.val :=
      (L2C.weight_eq_degree B w).trans (congrArg Subtype.val hw)
    have hviq : 0 < vexp iq := by
      simp only [vexp, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    have hvij : 0 < vexp ij := by
      simp only [vexp, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hij]
      omega
    have hvweight : L2C.weight B vexp = pkg.L := by
      simp only [vexp, map_add, L2C.weight_single, one_mul, hwdeg]
      change _ + (B.family iq).val + (B.family ij).val = pkg.L
      have hiq : (B.family iq).val = Q.q.val := rfl
      have hijw : (B.family ij).val = L2B.weights B pkg.j := rfl
      rw [hiq, hijw]
      have hqle := hpred.2.1
      rw [hpredWeight] at hqle
      have hnjpos := L2B.weights_positive B pkg.j
      have hnjle : L2B.weights B pkg.j ≤ pkg.L := by
        rw [hjdeg]
        nlinarith
      omega
    let v : L2C.FactorizationFiber B pkg.L := ⟨vexp, hvweight⟩
    obtain ⟨s, hpure, hspos⟩ := full_factorization_is_pure_of_sectorY_data
      P.M pkg.L pkg.L_pos pkg.tailComponentCount pkg.killedCount pkg.tailPure v
    by_cases hsi : s = iq
    · have hz := congrArg (fun z : Fin 4 →₀ ℕ => z ij) hpure
      simp [v, vexp, hsi, Finsupp.single_eq_of_ne hij] at hz hvij
    · have hz := congrArg (fun z : Fin 4 →₀ ℕ => z iq) hpure
      simp [v, vexp, Finsupp.single_eq_of_ne (Ne.symm hsi)] at hz hviq
  have humem : monomial u (1 : k) ∈ Q.J k :=
    (monomial_mem_chosen_iff_boundary k Q u).mpr huK
  have humin : u ∈ L3A.minimalExponents (Q.J k) := by
    refine ⟨humem, ?_⟩
    intro b hb hbu
    by_contra hub
    have hbr : b r < u r := by
      have hle := hbu r
      by_contra hn
      have hre : b r = u r := by omega
      apply hub
      intro s
      by_cases hsr : s = r
      · subst s; exact le_of_eq hre.symm
      · have huz : u s = 0 := by simp [u, Finsupp.single_eq_of_ne hsr]
        have hbs := hbu s
        omega
    have hbK := (monomial_mem_chosen_iff_boundary k Q b).mp hb
    have hbpred : L2B.weight Q (u - Finsupp.single r 1) ∈ Q.K := by
      have hb_le_pred : b ≤ u - Finsupp.single r 1 := by
        intro s
        by_cases hsr : s = r
        · subst s
          simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · have huz : u s = 0 := by simp [u, Finsupp.single_eq_of_ne hsr]
          have hbs := hbu s
          simp [huz, Finsupp.single_eq_of_ne hsr]
          omega
      let c := (u - Finsupp.single r 1) - b
      have hsum : b + c = u - Finsupp.single r 1 := by
        dsimp [c]
        rw [add_comm]
        exact tsub_add_cancel_of_le hb_le_pred
      have hcH : L2B.weight Q c ∈ Q.H := L3C.weight_mem_H Q c
      have hadd := aperyTail_add_mem Q.H_le hbK hcH
      change L2B.weight Q (u - Finsupp.single r 1) ∈
        aperyTail Gamma.toAddSubmonoid Q.H Q.q.val
      simpa only [← map_add, hsum] using hadd
    exact hpredNotK hbpred
  have hures : Nat.ModEq Q.q.val (L2B.weight Q u) 0 := by
    rw [hwu, hLq]
    simp [Nat.ModEq]
  exact ⟨r, a, u, ha, rfl, humin, hures⟩

theorem sectorY_repivot_q_fs_zero (k : Type*) [Field k]
    (P : P2Data Gamma) (pkg : SectorYPureFiberMonomialPivotPackage P) :
    let Q := L2C.atPivot P.M.base (P.M.base.order pkg.q.succ)
    L3A.q_fs (Q.J k) = 0 := by
  let Q := L2C.atPivot P.M.base (P.M.base.order pkg.q.succ)
  have hz : L2C.internalLoad Q Q.pivot = 0 := by
    simpa [Q] using pkg.zeroLoad
  obtain ⟨r, a, u, ha, hupure, humin, hures⟩ :=
    sectorY_repivot_residue_zero_minimal_generator k P pkg
  change (L3A.fullSupportGenerators (Q.J k)).ncard = 0
  rw [Set.ncard_eq_zero (hs := L3A.fullSupportGenerators_finite _)]
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  obtain ⟨v, hvstd, hgv⟩ := exists_standard_same_residue k Q g
  have hvzero := sectorY_full_support_first_stage k Q hz g hg v hvstd hgv
  have hgres : Nat.ModEq Q.q.val (L2B.weight Q g) 0 := by
    simpa only [hvzero, map_zero] using hgv
  exact sectorY_full_support_second_stage k Q hz u r a hupure ha humin hures g hg hgres

theorem sectorY_type_le_sourceCount
    (P : P2Data Gamma) (hY : SectorY P.M) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  classical
  let pkg := Classical.choice (sectorY_pure_fiber_monomial_pivot P hY)
  let Q := L2C.atPivot P.M.base (P.M.base.order pkg.q.succ)
  have hmon : L2B.IsMonomialIdeal ℚ (Q.J ℚ) := pkg.monomial ℚ
  have hqfs : L3A.q_fs (Q.J ℚ) = 0 := sectorY_repivot_q_fs_zero ℚ P pkg
  have hbound := L3A.support_refined_monomial_type_bound
    (L3A.chosenArtinianMonomial Q MonomialOrder.degLex hmon)
  change L3A.quotientType (Q.J ℚ) ≤
    L3A.mu (Q.J ℚ) + L3A.q_fs (Q.J ℚ) - 2 at hbound
  have hstrong : Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
    rw [L3A.chosen_type_eq (k := ℚ), L3A.chosen_mu_eq (k := ℚ), hqfs] at hbound
    simpa using hbound
  have hrho := p2_rho_eq_sourceCount_add_two P
  omega

end NS25Lean.L5A1
