import NS25Lean.P3IdealHeightsR61

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R62
variable {H : NumericalSemigroup}

def idealUnion (I J : RelativeIdeal H) : RelativeIdeal H where
  carrier := I.carrier ∪ J.carrier
  nonempty := by obtain ⟨x,hx⟩ := I.nonempty; exact ⟨x,Or.inl hx⟩
  bddBelow := by
    obtain ⟨l,hl⟩ := I.bddBelow
    obtain ⟨k,hk⟩ := J.bddBelow
    refine ⟨min l k,?_⟩
    rintro x (hx|hx)
    · exact le_trans (min_le_left _ _) (hl hx)
    · exact le_trans (min_le_right _ _) (hk hx)
  add_mem := by
    intro x h hx hh
    rcases hx with hx|hx
    · exact Or.inl (I.add_mem hx hh)
    · exact Or.inr (J.add_mem hx hh)

theorem union_aperyRepresentative (I J : RelativeIdeal H) (a : ℕ) [NeZero a] (s : ZMod a) :
    (idealUnion I J).aperyRepresentative a s =
      min (I.aperyRepresentative a s) (J.aperyRepresentative a s) := by
  apply le_antisymm
  · exact le_min
      ((idealUnion I J).aperyRepresentative_le a s (Or.inl (I.aperyRepresentative_mem a s))
        (I.aperyRepresentative_mod a s))
      ((idealUnion I J).aperyRepresentative_le a s (Or.inr (J.aperyRepresentative_mem a s))
        (J.aperyRepresentative_mod a s))
  · rcases (idealUnion I J).aperyRepresentative_mem a s with hx|hx
    · exact le_trans (min_le_left _ _) (I.aperyRepresentative_le a s hx
        ((idealUnion I J).aperyRepresentative_mod a s))
    · exact le_trans (min_le_right _ _) (J.aperyRepresentative_le a s hx
        ((idealUnion I J).aperyRepresentative_mod a s))

theorem translate_aperyRepresentative (I : RelativeIdeal H) (p : ℤ)
    (a : ℕ) [NeZero a] (s : ZMod a) :
    (I.translate p).aperyRepresentative a s = p+I.aperyRepresentative a (s-(p : ZMod a)) := by
  have hm : p+I.aperyRepresentative a (s-(p : ZMod a)) ∈ I.translate p := by
    change p+I.aperyRepresentative a (s-(p : ZMod a))-p ∈ I
    simpa using I.aperyRepresentative_mem a (s-(p : ZMod a))
  have hmod : ((p+I.aperyRepresentative a (s-(p : ZMod a)) : ℤ) : ZMod a) = s := by
    rw [Int.cast_add,I.aperyRepresentative_mod]; abel
  apply le_antisymm ((I.translate p).aperyRepresentative_le a s hm hmod)
  have hx := (I.translate p).aperyRepresentative_mem a s
  change (I.translate p).aperyRepresentative a s-p ∈ I at hx
  have hxmod : (((I.translate p).aperyRepresentative a s-p : ℤ) : ZMod a) = s-(p : ZMod a) := by
    rw [Int.cast_sub,(I.translate p).aperyRepresentative_mod]
  have hl := I.aperyRepresentative_le a (s-(p : ZMod a)) hx hxmod
  omega

theorem principal_union_aperyRepresentative (I : RelativeIdeal H) (p : ℤ)
    (a : ℕ) [NeZero a] (s : ZMod a) :
    (idealUnion I (H.asRelativeIdeal.translate p)).aperyRepresentative a s =
      min (I.aperyRepresentative a s) (p+H.asRelativeIdeal.aperyRepresentative a (s-(p : ZMod a))) := by
  rw [union_aperyRepresentative,translate_aperyRepresentative]

theorem exists_union_drop (I J : RelativeIdeal H) (a : ℕ) [NeZero a] (s : ZMod a) :
    ∃ k : ℕ, I.aperyRepresentative a s = (idealUnion I J).aperyRepresentative a s+(a : ℤ)*k := by
  apply RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a
  · rw [union_aperyRepresentative]; exact min_le_left _ _
  · rw [I.aperyRepresentative_mod,(idealUnion I J).aperyRepresentative_mod]

def insertionDrop (I J : RelativeIdeal H) (a : ℕ) [NeZero a] (s : ZMod a) : ℕ :=
  Classical.choose (exists_union_drop I J a s)

theorem insertionDrop_eq (I J : RelativeIdeal H) (a : ℕ) [NeZero a] (s : ZMod a) :
    I.aperyRepresentative a s = (idealUnion I J).aperyRepresentative a s+(a : ℤ)*insertionDrop I J a s :=
  Classical.choose_spec (exists_union_drop I J a s)

theorem insertion_step_eq (I J : RelativeIdeal H) (a h : ℕ) [NeZero a]
    (hh : h ∈ H) (s : ZMod a) :
    ((idealUnion I J).aperyStepQuotient a h hh s : ℤ) =
      (I.aperyStepQuotient a h hh s : ℤ)-insertionDrop I J a s+insertionDrop I J a (s+h) := by
  have hi := I.apery_step_eq a h hh s
  have hf := (idealUnion I J).apery_step_eq a h hh s
  have h0 := insertionDrop_eq I J a s
  have h1 := insertionDrop_eq I J a (s+h)
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  nlinarith

theorem union_minimalGenerator_iff (I J : RelativeIdeal H) (x : ℤ) :
    (idealUnion I J).IsMinimalGenerator x ↔
      (I.IsMinimalGenerator x ∧ ∀ h : ℕ, h ∈ H → h ≠ 0 → x-h ∉ J) ∨
      (J.IsMinimalGenerator x ∧ ∀ h : ℕ, h ∈ H → h ≠ 0 → x-h ∉ I) := by
  constructor
  · intro hx
    rcases hx.1 with hi|hj
    · exact Or.inl ⟨⟨hi,fun h hh hn hsub => hx.2 h hh hn (Or.inl hsub)⟩,
        fun h hh hn hsub => hx.2 h hh hn (Or.inr hsub)⟩
    · exact Or.inr ⟨⟨hj,fun h hh hn hsub => hx.2 h hh hn (Or.inr hsub)⟩,
        fun h hh hn hsub => hx.2 h hh hn (Or.inl hsub)⟩
  · rintro (⟨hi,hj⟩|⟨hj,hi⟩)
    · refine ⟨Or.inl hi.1,?_⟩
      rintro h hh hn (hx|hx)
      · exact hi.2 h hh hn hx
      · exact hj h hh hn hx
    · refine ⟨Or.inr hj.1,?_⟩
      rintro h hh hn (hx|hx)
      · exact hi h hh hn hx
      · exact hj.2 h hh hn hx

end NS25Lean.P3R62
