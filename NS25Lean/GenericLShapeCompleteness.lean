import NS25Lean.P2SectorB

set_option linter.style.header false
noncomputable section

namespace NS25Lean.GenericLShape

open L5A2B

/-- Payload-independent finite indexing of a Herzog L-shape. -/
abbrev Index (p q z v : ℕ) :=
  (Fin p × Fin (q + v)) ⊕ (Fin z × Fin q)

def pair (p q z v : ℕ) : Index p q z v → ℤ × ℤ
  | Sum.inl ij => (ij.1.val, ij.2.val)
  | Sum.inr sj => (p + sj.1.val, sj.2.val)

def residue (a b c p q z v : ℕ) (x : Index p q z v) : ZMod a :=
  ((pair p q z v x).1 * b + (pair p q z v x).2 * c : ℤ)

theorem pair_mem {p q z v : ℕ} (x : Index p q z v) :
    InLShape p q z v (pair p q z v x).1 (pair p q z v x).2 := by
  rcases x with ij | sj
  · rcases ij with ⟨i, j⟩
    simp only [pair]
    unfold InLShape
    constructor
    · exact_mod_cast i.val.zero_le
    constructor
    · exact_mod_cast j.val.zero_le
    constructor
    · exact_mod_cast lt_of_lt_of_le i.isLt (Nat.le_add_right p z)
    constructor
    · exact_mod_cast j.isLt
    · left
      exact_mod_cast i.isLt
  · rcases sj with ⟨s, j⟩
    simp only [pair]
    unfold InLShape
    norm_num
    omega

theorem exists_index_of_mem {p q z v : ℕ} {i j : ℤ}
    (h : InLShape p q z v i j) :
    ∃ x : Index p q z v, pair p q z v x = (i, j) := by
  rcases h with ⟨hi0, hj0, hibound, hjbound, hcorner⟩
  by_cases hip : i < (p : ℤ)
  · let ii : Fin p := ⟨i.toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hip⟩
    let jj : Fin (q + v) := ⟨j.toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hjbound⟩
    refine ⟨Sum.inl (ii, jj), ?_⟩
    simp [pair, ii, jj, Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0]
  · have hpi : (p : ℤ) ≤ i := le_of_not_gt hip
    have hjq : j < (q : ℤ) := hcorner.resolve_left hip
    have hisub0 : 0 ≤ i - (p : ℤ) := by omega
    have hisubz : i - (p : ℤ) < (z : ℤ) := by omega
    let ss : Fin z := ⟨(i - (p : ℤ)).toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hisubz⟩
    let jj : Fin q := ⟨j.toNat, by
      exact (Int.toNat_lt_of_ne_zero (by omega)).2 hjq⟩
    refine ⟨Sum.inr (ss, jj), ?_⟩
    simp [pair, ss, jj, Int.toNat_of_nonneg hisub0,
      Int.toNat_of_nonneg hj0]
    omega

private theorem cross_impossible
    (a b c c2 c3 p q z v : ℕ)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    {i j i' j' : ℤ}
    (hmod : Int.ModEq a (i * b + j * c) (i' * b + j' * c))
    (hiStrict : i' < i) (hjStrict : j < j')
    (hi'Nonneg : 0 ≤ i') (hjNonneg : 0 ≤ j)
    (hiBound : i < (p + z : ℕ)) (hjBound : j' < (q + v : ℕ)) : False := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  let I := (i - i').toNat
  let J := (j' - j).toNat
  have hIZ : (I : ℤ) = i - i' := Int.toNat_of_nonneg (by omega)
  have hJZ : (J : ℤ) = j' - j := Int.toNat_of_nonneg (by omega)
  have hIpos : 0 < I := by omega
  have hJpos : 0 < J := by omega
  have hIlt : I < p + z := by omega
  have hJlt : J < q + v := by omega
  by_cases hk0 : 0 ≤ k
  · let K := k.toNat
    have hKZ : (K : ℤ) = k := Int.toNat_of_nonneg hk0
    have hrel : J * c = K * a + I * b := by
      exact_mod_cast (show (J : ℤ) * c = (K : ℤ) * a + (I : ℤ) * b by
        rw [hIZ, hJZ, hKZ]
        nlinarith)
    have := hmin3 J K I hJpos hrel
    omega
  · have hkneg : k < 0 := lt_of_not_ge hk0
    let K := (-k).toNat
    have hKZ : (K : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hrel : I * b = K * a + J * c := by
      exact_mod_cast (show (I : ℤ) * b = (K : ℤ) * a + (J : ℤ) * c by
        rw [hIZ, hJZ, hKZ]
        nlinarith)
    have := hmin2 I K J hIpos hrel
    omega

theorem modEq_unique
    (a b c c2 c3 p q z v : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hz : 0 < z) (hv : 0 < v)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    (hunique : UniqueZeroInLShape a b c p q z v)
    {i j i' j' : ℤ}
    (hshape : InLShape p q z v i j)
    (hshape' : InLShape p q z v i' j')
    (hmod : Int.ModEq a (i * b + j * c) (i' * b + j' * c)) :
    i = i' ∧ j = j' := by
  rcases hshape with ⟨hi0, hj0, hi, hj, hcorner⟩
  rcases hshape' with ⟨hi0', hj0', hi', hj', hcorner'⟩
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  by_cases hii : i' ≤ i
  · by_cases hjj : j' ≤ j
    · have hdshape : InLShape p q z v (i - i') (j - j') := by
        unfold InLShape
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        · rcases hcorner with hip | hjq
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      have hzero : RepresentsZero a b c (i - i') (j - j') := by
        refine ⟨-k, ?_⟩
        nlinarith
      obtain ⟨hieq, hjeq⟩ := hunique _ _ hdshape hzero
      omega
    · have hjcross : j < j' := lt_of_not_ge hjj
      have hiStrict : i' < i := by
        by_contra hn
        have hieq : i = i' := by omega
        subst i'
        have hdshape : InLShape p q z v 0 (j' - j) := by
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
        have hzero : RepresentsZero a b c 0 (j' - j) := by
          refine ⟨k, ?_⟩
          nlinarith
        have := hunique _ _ hdshape hzero
        omega
      exact False.elim (cross_impossible a b c c2 c3 p q z v hs2 hs3
        hmin2 hmin3 hmod hiStrict hjcross hi0' hj0 hi hj')
  · have hiCross : i < i' := lt_of_not_ge hii
    by_cases hjj : j ≤ j'
    · have hdshape : InLShape p q z v (i' - i) (j' - j) := by
        unfold InLShape
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        constructor
        · omega
        · rcases hcorner' with hip | hjq
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      have hzero : RepresentsZero a b c (i' - i) (j' - j) := by
        refine ⟨k, ?_⟩
        nlinarith
      obtain ⟨hieq, hjeq⟩ := hunique _ _ hdshape hzero
      omega
    · have hjCross : j' < j := lt_of_not_ge hjj
      exact False.elim (cross_impossible a b c c2 c3 p q z v hs2 hs3
        hmin2 hmin3 hmod.symm hiCross hjCross hi0 hj0' hi' hj)

theorem residue_injective
    (a b c c2 c3 p q z v : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hz : 0 < z) (hv : 0 < v)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    (hunique : UniqueZeroInLShape a b c p q z v) :
    Function.Injective (residue a b c p q z v) := by
  intro x y hxy
  have hcoords := modEq_unique a b c c2 c3 p q z v hp hq hz hv hs2 hs3
    hmin2 hmin3 hunique (pair_mem x) (pair_mem y)
    ((ZMod.intCast_eq_intCast_iff _ _ _).mp hxy)
  rcases x with x | x <;> rcases y with y | y
  · rcases x with ⟨xi, xj⟩
    rcases y with ⟨yi, yj⟩
    simp only [pair] at hcoords
    cases Fin.ext (by omega : xi.val = yi.val)
    cases Fin.ext (by omega : xj.val = yj.val)
    rfl
  · rcases x with ⟨xi, xj⟩
    rcases y with ⟨ys, yj⟩
    simp only [pair] at hcoords
    exfalso
    have hylt : (ys.val : ℤ) < z := by exact_mod_cast ys.isLt
    have hxlt : (xi.val : ℤ) < p := by exact_mod_cast xi.isLt
    omega
  · rcases x with ⟨xs, xj⟩
    rcases y with ⟨yi, yj⟩
    simp only [pair] at hcoords
    exfalso
    have hxlt : (xs.val : ℤ) < z := by exact_mod_cast xs.isLt
    have hylt : (yi.val : ℤ) < p := by exact_mod_cast yi.isLt
    omega
  · rcases x with ⟨xs, xj⟩
    rcases y with ⟨ys, yj⟩
    simp only [pair] at hcoords
    cases Fin.ext (by omega : xs.val = ys.val)
    cases Fin.ext (by omega : xj.val = yj.val)
    rfl

theorem card_dvd
    (a b c c1 c2 c3 p q z v u w : ℕ)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hrel2 : c2 * b = u * a + v * c)
    (hrel3 : c3 * c = w * a + z * b)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) :
    a ∣ p * (q + v) + z * q := by
  let N := p * (q + v) + z * q
  have hNb : N * b = (q * u + v * c1) * a := by
    dsimp [N]
    calc
      (p * (q + v) + z * q) * b =
          q * ((p + z) * b) + v * (p * b) := by ring
      _ = q * (u * a + v * c) + v * (p * b) := by rw [← hs2, hrel2]
      _ = q * u * a + v * (p * b + q * c) := by ring
      _ = q * u * a + v * (c1 * a) := by rw [← hrel1]
      _ = (q * u + v * c1) * a := by ring
  have hNc : N * c = (p * w + z * c1) * a := by
    dsimp [N]
    calc
      (p * (q + v) + z * q) * c =
          p * ((q + v) * c) + z * (q * c) := by ring
      _ = p * (w * a + z * b) + z * (q * c) := by rw [← hs3, hrel3]
      _ = p * w * a + z * (p * b + q * c) := by ring
      _ = p * w * a + z * (c1 * a) := by rw [← hrel1]
      _ = (p * w + z * c1) * a := by ring
  have hab : a ∣ N * b := by rw [hNb]; exact dvd_mul_left _ _
  have hac : a ∣ N * c := by rw [hNc]; exact dvd_mul_left _ _
  have hag : a ∣ Nat.gcd (N * b) (N * c) := Nat.dvd_gcd hab hac
  rw [Nat.gcd_mul_left] at hag
  exact (show Nat.Coprime a (Nat.gcd b c) from hgcd).dvd_of_dvd_mul_right hag

/-- Generic finite L-shape completeness, with no branch payload. -/
theorem residue_bijective
    (a b c c1 c2 c3 p q z v u w : ℕ)
    (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) (hz : 0 < z) (hv : 0 < v)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hrel2 : c2 * b = u * a + v * c)
    (hrel3 : c3 * c = w * a + z * b)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    (hunique : UniqueZeroInLShape a b c p q z v)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) :
    Function.Bijective (residue a b c p q z v) := by
  let f := residue a b c p q z v
  have hinj : Function.Injective f := residue_injective a b c c2 c3 p q z v
    hp hq hz hv hs2 hs3 hmin2 hmin3 hunique
  letI : NeZero a := ⟨ha.ne'⟩
  have hcardIndex : Fintype.card (Index p q z v) = p * (q + v) + z * q := by
    simp [Index]
  have hle : p * (q + v) + z * q ≤ a := by
    rw [← hcardIndex, ← ZMod.card a]
    exact Fintype.card_le_of_injective f hinj
  have hpos : 0 < p * (q + v) + z * q := by positivity
  have hge : a ≤ p * (q + v) + z * q :=
    Nat.le_of_dvd hpos (card_dvd a b c c1 c2 c3 p q z v u w
      hs2 hs3 hrel1 hrel2 hrel3 hgcd)
  have hcard : Fintype.card (Index p q z v) = Fintype.card (ZMod a) := by
    rw [hcardIndex, ZMod.card]
    omega
  exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩

theorem existsUnique_pair
    (a b c c1 c2 c3 p q z v u w : ℕ)
    (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) (hz : 0 < z) (hv : 0 < v)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hrel2 : c2 * b = u * a + v * c)
    (hrel3 : c3 * c = w * a + z * b)
    (hmin2 : ∀ n x y : ℕ, 0 < n → n * b = x * a + y * c → c2 ≤ n)
    (hmin3 : ∀ n x y : ℕ, 0 < n → n * c = x * a + y * b → c3 ≤ n)
    (hunique : UniqueZeroInLShape a b c p q z v)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) (n : ℤ) :
    ∃! ij : ℤ × ℤ,
      InLShape p q z v ij.1 ij.2 ∧ Int.ModEq a (ij.1 * b + ij.2 * c) n := by
  let f := residue a b c p q z v
  have hbij := residue_bijective a b c c1 c2 c3 p q z v u w ha hp hq hz hv
    hs2 hs3 hrel1 hrel2 hrel3 hmin2 hmin3 hunique hgcd
  obtain ⟨x, hx, hxuniq⟩ := hbij.existsUnique (n : ZMod a)
  refine ⟨pair p q z v x, ⟨pair_mem x, ?_⟩, ?_⟩
  · exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hx
  · intro ij hij
    obtain ⟨y, hyPair⟩ := exists_index_of_mem hij.1
    have hy : f y = (n : ZMod a) := by
      apply (ZMod.intCast_eq_intCast_iff _ _ _).2
      simpa [f, residue, hyPair] using hij.2
    have hyx : y = x := hxuniq y hy
    calc
      ij = pair p q z v y := hyPair.symm
      _ = pair p q z v x := by rw [hyx]

/-- The natural-coordinate form of the same L-shape. -/
def NatDomain (c2 c3 p q i j : ℕ) : Prop :=
  i < c2 ∧ j < c3 ∧ (i < p ∨ j < q)

/-- Terminating Herzog reduction.  The strong-induction measure is the
represented value `x*b+y*c`; every nonterminal step removes a positive
multiple of `a`. -/
theorem exists_reduction
    (a b c c1 c2 c3 p q z v u w : ℕ)
    (ha : 0 < a) (hc1 : 0 < c1) (hu : 0 < u) (hw : 0 < w)
    (hs2 : c2 = p + z) (hs3 : c3 = q + v)
    (hrel1 : c1 * a = p * b + q * c)
    (hrel2 : c2 * b = u * a + v * c)
    (hrel3 : c3 * c = w * a + z * b)
    (x y : ℕ) :
    ∃ i j k : ℕ,
      NatDomain c2 c3 p q i j ∧
        x * b + y * c = i * b + j * c + k * a := by
  let P : ℕ → Prop := fun n =>
    ∀ x y : ℕ, x * b + y * c = n →
      ∃ i j k : ℕ,
        NatDomain c2 c3 p q i j ∧
          x * b + y * c = i * b + j * c + k * a
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hvalue
      by_cases hx : c2 ≤ x
      · let x' := x - c2
        let y' := y + v
        have hxcancel : x' + c2 = x := Nat.sub_add_cancel hx
        have hstep : x * b + y * c = x' * b + y' * c + u * a := by
          dsimp [x', y']
          nlinarith only [hxcancel, hrel2]
        have hpositive : 0 < u * a := Nat.mul_pos hu ha
        have hlt : x' * b + y' * c < n := by omega
        obtain ⟨i, j, k, hdom, heq⟩ := ih _ hlt x' y' rfl
        refine ⟨i, j, k + u, hdom, ?_⟩
        rw [hstep, heq]
        ring
      · by_cases hy : c3 ≤ y
        · let x' := x + z
          let y' := y - c3
          have hycancel : y' + c3 = y := Nat.sub_add_cancel hy
          have hstep : x * b + y * c = x' * b + y' * c + w * a := by
            dsimp [x', y']
            nlinarith only [hycancel, hrel3]
          have hpositive : 0 < w * a := Nat.mul_pos hw ha
          have hlt : x' * b + y' * c < n := by omega
          obtain ⟨i, j, k, hdom, heq⟩ := ih _ hlt x' y' rfl
          refine ⟨i, j, k + w, hdom, ?_⟩
          rw [hstep, heq]
          ring
        · by_cases hcorner : p ≤ x ∧ q ≤ y
          · let x' := x - p
            let y' := y - q
            have hxcancel : x' + p = x := Nat.sub_add_cancel hcorner.1
            have hycancel : y' + q = y := Nat.sub_add_cancel hcorner.2
            have hstep : x * b + y * c = x' * b + y' * c + c1 * a := by
              dsimp [x', y']
              nlinarith only [hxcancel, hycancel, hrel1]
            have hpositive : 0 < c1 * a := Nat.mul_pos hc1 ha
            have hlt : x' * b + y' * c < n := by omega
            obtain ⟨i, j, k, hdom, heq⟩ := ih _ hlt x' y' rfl
            refine ⟨i, j, k + c1, hdom, ?_⟩
            rw [hstep, heq]
            ring
          · refine ⟨x, y, 0, ?_, by simp⟩
            exact ⟨lt_of_not_ge hx, lt_of_not_ge hy, by omega⟩
  exact hP (x * b + y * c) x y rfl

end NS25Lean.GenericLShape
