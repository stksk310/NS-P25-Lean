import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace NS25Lean.SharedCap

abbrev Monomial := ℕ × ℕ × ℕ
def Below (a b : Monomial) : Prop := a.1  ≤  b.1 ∧ a.2.1  ≤  b.2.1 ∧ a.2.2  ≤  b.2.2
def Closure (G : Set Monomial) : Set Monomial := {p | ∃ g ∈ G, Below g p}
def Wrap (u v : ℕ) (g : Monomial) : Monomial := (g.1 + u, 0, g.2.2 + v)
def ZeroGenerators (O : Set Monomial) : Set Monomial := {g ∈ O | g.2.1 = 0}
def MGenerators (O : Set Monomial) (u v : ℕ) : Set Monomial :=
  O ∪ {p | ∃ g ∈ O, 0 < g.2.1 ∧ p = Wrap u v g}
def LGenerators (O : Set Monomial) (C u v : ℕ) : Set Monomial :=
  insert (0,C,0) (MGenerators O u v)
def MinimalGenerator (G : Set Monomial) (p : Monomial) : Prop :=
  p ∈ Closure G ∧ ∀ q ∈ Closure G, Below q p → q = p
def Socle (G : Set Monomial) (p : Monomial) : Prop :=
  p ∉ Closure G ∧ (p.1+1,p.2.1,p.2.2) ∈ Closure G ∧
    (p.1,p.2.1+1,p.2.2) ∈ Closure G ∧ (p.1,p.2.1,p.2.2+1) ∈ Closure G

/-- Precisely the structural cap/attainment hypotheses, with no count or
exceptional-witness conclusion stored as data. -/
structure Data where
  C : ℕ
  u : ℕ
  v : ℕ
  U : ℕ
  V : ℕ
  C_pos : 0 < C
  u_pos : 0 < u
  v_pos : 0 < v
  U_pos : 0 < U
  V_pos : 0 < V
  originals : Set Monomial
  originals_finite : originals.Finite
  first : Monomial
  first_mem : first ∈ originals
  first_y_pos : 0 < first.2.1
  first_transverse_pos : 0 < first.1 + first.2.2
  normal : ∀ g ∈ originals, g.2.1 < C
  shape : ∀ g ∈ originals, g ≠ first → 0 < g.2.1 →
    (U  ≤  g.1 ∧ g.2.2 = 0) ∨ (V  ≤  g.2.2 ∧ g.1 = 0)
  other_wraps : ∀ g ∈ originals, g ≠ first → 0 < g.2.1 →
    Wrap u v g ∈ Closure (ZeroGenerators originals)
  rectangle : ∀ i k, i < u+U → k < v+V →
    (i,0,k) ∉ Closure (ZeroGenerators originals)
  central : ∀ i k, u  ≤  i → v  ≤  k →
    ((i,0,k) ∉ Closure (ZeroGenerators originals) ↔ i < u+U ∧ k < v+V)
  attained_x : 0 < first.2.2 → ∃ g ∈ originals,
    g ≠ first ∧ g.1 = U ∧ 0 < g.2.1 ∧ g.2.2 = 0
  attained_z : 0 < first.1 → ∃ g ∈ originals,
    g ≠ first ∧ g.1 = 0 ∧ 0 < g.2.1 ∧ g.2.2 = V

def Data.additionalWraps (D : Data) : Set Monomial :=
  {p | MinimalGenerator (LGenerators D.originals D.C D.u D.v) p ∧ p ∉ D.originals ∧
    ∃ g ∈ D.originals, 0 < g.2.1 ∧ p = Wrap D.u D.v g}
def Data.fullSupport (D : Data) : ℕ := if 0 < D.first.1 ∧ 0 < D.first.2.2 then 1 else 0
def Data.exceptional (D : Data) : Set Monomial :=
  {p | Socle (LGenerators D.originals D.C D.u D.v) p ∧ p.2.1+1=D.C ∧
    Wrap D.u D.v p ∉ Closure (MGenerators D.originals D.u D.v)}

theorem below_refl (p : Monomial) : Below p p := ⟨le_rfl,le_rfl,le_rfl⟩
theorem below_trans {p q r : Monomial} (hpq : Below p q) (hqr : Below q r) : Below p r :=
  ⟨hpq.1.trans hqr.1,hpq.2.1.trans hqr.2.1,hpq.2.2.trans hqr.2.2⟩
theorem below_antisymm {p q : Monomial} (hpq : Below p q) (hqp : Below q p) : p=q := by
  rcases p with ⟨x,y,z⟩;rcases q with ⟨a,b,c⟩
  simp only [Below] at hpq hqp
  congr <;> omega
theorem closure_upward {G : Set Monomial} {p q : Monomial}
    (hp : p ∈ Closure G) (hpq : Below p q) : q ∈ Closure G := by
  obtain ⟨g,hg,he⟩:=hp
  exact ⟨g,hg,below_trans he hpq⟩

theorem original_mem_M {O : Set Monomial} {u v : ℕ} {p : Monomial} (hp : p∈O) :
    p ∈ MGenerators O u v := Or.inl hp
theorem zero_closure_le_M (O : Set Monomial) (u v : ℕ) :
    Closure (ZeroGenerators O) ⊆ Closure (MGenerators O u v) := by
  rintro p ⟨g,hg,he⟩
  exact ⟨g,Or.inl hg.1,he⟩

theorem exceptional_transverse_bounds (D : Data) {p : Monomial} (hp : p∈D.exceptional) :
    p.1<D.U ∧ p.2.2<D.V := by
  have hn : Wrap D.u D.v p ∉ Closure (ZeroGenerators D.originals) :=
    fun h => hp.2.2 (zero_closure_le_M D.originals D.u D.v h)
  have hc := (D.central (p.1+D.u) (p.2.2+D.v) (by omega) (by omega)).mp hn
  omega

theorem exceptional_finite (D : Data) : D.exceptional.Finite := by
  let s := ((Finset.range D.U).product (Finset.range D.V)).image
    (fun q : ℕ×ℕ => (q.1,D.C-1,q.2))
  apply (s.finite_toSet).subset
  intro p hp
  obtain ⟨hi,hk⟩:=exceptional_transverse_bounds D hp
  apply Finset.mem_image.mpr
  refine ⟨(p.1,p.2.2),Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi,Finset.mem_range.mpr hk⟩,?_⟩
  have hy : p.2.1=D.C-1 := by have :=hp.2.1;omega
  rcases p with ⟨i,j,k⟩
  simpa only [Prod.mk.injEq, true_and, and_true] using hy.symm

theorem first_wrap_standard_iff (D : Data) :
    Wrap D.u D.v D.first ∉ Closure (ZeroGenerators D.originals) ↔
      D.first.1<D.U ∧ D.first.2.2<D.V := by
  have h := D.central (D.first.1+D.u) (D.first.2.2+D.v) (by omega) (by omega)
  change ((D.first.1+D.u,0,D.first.2.2+D.v) ∉ Closure (ZeroGenerators D.originals)) ↔ _
  rw [h]
  omega

theorem minimal_zero_mem_original (D : Data) {p : Monomial}
    (hm : MinimalGenerator (LGenerators D.originals D.C D.u D.v) p)
    (hp : p∈Closure (ZeroGenerators D.originals)) : p∈D.originals := by
  obtain ⟨g,hg,hd⟩:=hp
  have hgL : g∈Closure (LGenerators D.originals D.C D.u D.v) :=
    ⟨g,Or.inr (Or.inl hg.1),below_refl g⟩
  exact (hm.2 g hgL hd) ▸ hg.1

theorem additional_subset_first (D : Data) : D.additionalWraps ⊆ {Wrap D.u D.v D.first} := by
  rintro p ⟨hm,hnot,⟨g,hg,hy,rfl⟩⟩
  by_cases he : g=D.first
  · subst g;exact rfl
  · exact (hnot (minimal_zero_mem_original D hm (D.other_wraps g hg he hy))).elim

theorem first_wrap_minimal (D : Data)
    (hn : Wrap D.u D.v D.first ∉ Closure (ZeroGenerators D.originals)) :
    MinimalGenerator (LGenerators D.originals D.C D.u D.v) (Wrap D.u D.v D.first) := by
  refine ⟨⟨_,Or.inr (Or.inr ⟨D.first,D.first_mem,D.first_y_pos,rfl⟩),below_refl _⟩,?_⟩
  intro q hq hqw
  obtain ⟨g,hg,hgq⟩:=hq
  have hgw := below_trans hgq hqw
  rcases hg with rfl | hg
  · have :=hgw.2.1;have :=D.C_pos;simp only [Wrap] at *;omega
  · rcases hg with hg | ⟨a,ha,hay,rfl⟩
    · have hz : g.2.1=0 := by have:=hgw.2.1;change g.2.1 ≤ 0 at this;omega
      exact (hn ⟨g,⟨hg,hz⟩,hgw⟩).elim
    · by_cases he : a=D.first
      · subst a;exact below_antisymm hqw hgq
      · exact (hn (closure_upward (D.other_wraps a ha he hay) hgw)).elim

theorem first_wrap_not_original (D : Data)
    (hn : Wrap D.u D.v D.first ∉ Closure (ZeroGenerators D.originals)) :
    Wrap D.u D.v D.first ∉ D.originals := by
  intro ho
  exact hn ⟨Wrap D.u D.v D.first,⟨ho,rfl⟩,below_refl _⟩

theorem additional_eq (D : Data) : D.additionalWraps =
    if D.first.1<D.U ∧ D.first.2.2<D.V then {Wrap D.u D.v D.first} else ∅ := by
  classical
  by_cases h : D.first.1<D.U ∧ D.first.2.2<D.V
  · rw [ite_eq_left h]
    apply Set.Subset.antisymm (additional_subset_first D)
    rintro p rfl
    have hn :=(first_wrap_standard_iff D).mpr h
    exact ⟨first_wrap_minimal D hn,first_wrap_not_original D hn,
      D.first,D.first_mem,D.first_y_pos,rfl⟩
  · rw [ite_eq_right h]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have he : p=Wrap D.u D.v D.first := additional_subset_first D hp
    subst p
    have hn : Wrap D.u D.v D.first ∉ Closure (ZeroGenerators D.originals) :=
      fun hc =>hp.2.1 (minimal_zero_mem_original D hp.1 hc)
    exact h ((first_wrap_standard_iff D).mp hn)

theorem additional_wrap_count (D : Data) : D.additionalWraps.ncard =
    if D.first.1<D.U ∧ D.first.2.2<D.V then 1 else 0 := by
  classical
  rw [additional_eq]
  split_ifs <;> simp

theorem originals_not_divide_top (D : Data) (i k : ℕ) (hi : i<D.U) (hk : k<D.V)
    (hfirst : ¬(D.first.1  ≤  i ∧ D.first.2.2  ≤  k)) :
    ∀ g∈D.originals, ¬Below g (i,D.C-1,k) := by
  intro g hg hd
  change g.1 ≤ i ∧ g.2.1 ≤ D.C-1 ∧ g.2.2 ≤ k at hd
  by_cases hy : g.2.1=0
  · exact D.rectangle i k (by omega) (by omega)
      ⟨g,⟨hg,hy⟩,⟨hd.1,by omega,hd.2.2⟩⟩
  · by_cases he : g=D.first
    · subst g;exact hfirst ⟨hd.1,hd.2.2⟩
    · rcases D.shape g hg he (by omega) with hx | hz
      · have :=hd.1;omega
      · have :=hd.2.2;omega

theorem top_standard (D : Data) (i k : ℕ) (hi : i<D.U) (hk : k<D.V)
    (hfirst : ¬(D.first.1  ≤  i ∧ D.first.2.2  ≤  k)) :
    (i,D.C-1,k) ∉ Closure (LGenerators D.originals D.C D.u D.v) := by
  rintro ⟨g,hg,hd⟩
  change g.1 ≤ i ∧ g.2.1 ≤ D.C-1 ∧ g.2.2 ≤ k at hd
  rcases hg with rfl | hg
  · have hc : D.C  ≤  D.C-1 := hd.2.1
    have hcp := D.C_pos
    omega
  · rcases hg with hg | ⟨a,ha,hay,rfl⟩
    · exact originals_not_divide_top D i k hi hk hfirst g hg hd
    · apply originals_not_divide_top D i k hi hk hfirst a ha
      have hn:=D.normal a ha
      change a.1 ≤ i ∧ a.2.1 ≤ D.C-1 ∧ a.2.2 ≤ k
      have hx : a.1+D.u ≤ i := hd.1
      have hz : a.2.2+D.v ≤ k := hd.2.2
      exact ⟨by omega,by omega,by omega⟩

theorem top_translate_standard (D : Data) (i k : ℕ) (hi : i<D.U) (hk : k<D.V)
    (hfirst : ¬(D.first.1  ≤  i ∧ D.first.2.2  ≤  k)) :
    Wrap D.u D.v (i,D.C-1,k) ∉ Closure (MGenerators D.originals D.u D.v) := by
  have hn := D.rectangle (i+D.u) (k+D.v) (by omega) (by omega)
  rintro ⟨g,hg,hd⟩
  change g.1 ≤ i+D.u ∧ g.2.1 ≤ 0 ∧ g.2.2 ≤ k+D.v at hd
  rcases hg with hg | ⟨a,ha,hay,rfl⟩
  · have hy : g.2.1=0 := by have :=hd.2.1;change g.2.1 ≤ 0 at this;omega
    exact hn ⟨g,⟨hg,hy⟩,hd⟩
  · by_cases he : a=D.first
    · subst a
      apply hfirst
      have hx:=hd.1;have hz:=hd.2.2
      change D.first.1+D.u ≤ i+D.u at hx
      change D.first.2.2+D.v ≤ k+D.v at hz
      omega
    · exact hn (closure_upward (D.other_wraps a ha he hay) hd)

theorem first_blocker (D : Data) (i k : ℕ) (hi : D.first.1  ≤  i) (hk : D.first.2.2  ≤  k) :
    ∃ g∈D.originals, Below g (i,D.C-1,k) := by
  have hn:=D.normal D.first D.first_mem
  refine ⟨D.first,D.first_mem,?_⟩
  change D.first.1  ≤  i ∧ D.first.2.1  ≤  D.C-1 ∧ D.first.2.2  ≤  k
  exact ⟨hi,by omega,hk⟩

theorem x_blocker (D : Data) (i k : ℕ) (hgamma : 0 < D.first.2.2) (hi : D.U  ≤  i) :
    ∃ g∈D.originals, Below g (i,D.C-1,k) := by
  obtain ⟨g,hg,_,hx,hy,hz⟩:=D.attained_x hgamma
  have hn:=D.normal g hg
  refine ⟨g,hg,?_⟩
  change g.1  ≤  i ∧ g.2.1  ≤  D.C-1 ∧ g.2.2  ≤  k
  exact ⟨by omega,by omega,by omega⟩

theorem z_blocker (D : Data) (i k : ℕ) (halpha : 0<D.first.1) (hk : D.V ≤ k) :
    ∃ g∈D.originals, Below g (i,D.C-1,k) := by
  obtain ⟨g,hg,_,hx,hy,hz⟩:=D.attained_z halpha
  have hn:=D.normal g hg
  refine ⟨g,hg,?_⟩
  change g.1  ≤  i ∧ g.2.1  ≤  D.C-1 ∧ g.2.2  ≤  k
  exact ⟨by omega,by omega,by omega⟩

theorem exceptional_of_blockers (D : Data) (i k : ℕ) (hi : i<D.U) (hk : k<D.V)
    (hfirst : ¬(D.first.1  ≤  i ∧ D.first.2.2  ≤  k))
    (hx : ∃g∈D.originals, Below g (i+1,D.C-1,k))
    (hz : ∃g∈D.originals, Below g (i,D.C-1,k+1)) :
    (i,D.C-1,k) ∈ D.exceptional := by
  obtain ⟨gx,hgx,hbx⟩:=hx
  obtain ⟨gz,hgz,hbz⟩:=hz
  refine ⟨⟨top_standard D i k hi hk hfirst,
    ⟨gx,Or.inr (Or.inl hgx),hbx⟩,?_,⟨gz,Or.inr (Or.inl hgz),hbz⟩⟩,
    ?_,top_translate_standard D i k hi hk hfirst⟩
  · refine ⟨(0,D.C,0),Or.inl rfl,?_⟩
    have :=D.C_pos
    change 0 ≤ i ∧ D.C ≤ D.C-1+1 ∧ 0 ≤ k
    exact ⟨by omega,by omega,by omega⟩
  · change D.C-1+1=D.C
    have :=D.C_pos;omega

theorem one_le_exceptional_of_mem (D : Data) {p : Monomial} (hp : p∈D.exceptional) :
    1 ≤ D.exceptional.ncard := by
  have h := (Set.ncard_pos (exceptional_finite D)).mpr ⟨p,hp⟩
  omega

theorem two_le_exceptional_of_mem (D : Data) {p q : Monomial}
    (hp : p∈D.exceptional) (hq : q∈D.exceptional) (hne : p≠q) : 2 ≤ D.exceptional.ncard := by
  have hs : ({p,q}:Set Monomial) ⊆ D.exceptional := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hp
    · exact hq
  have hn:=Set.ncard_le_ncard hs (exceptional_finite D)
  rwa [Set.ncard_pair hne] at hn

theorem full_inner_two (D : Data) (ha : 0 < D.first.1) (hg : 0 < D.first.2.2)
    (hau : D.first.1 < D.U) (hgv : D.first.2.2 < D.V) : 2 ≤ D.exceptional.ncard := by
  have hU := D.U_pos;have hV := D.V_pos
  have hp : (D.first.1-1,D.C-1,D.V-1) ∈ D.exceptional := by
    apply exceptional_of_blockers D (D.first.1-1) (D.V-1) (by omega) (by omega)
    · rintro ⟨h,_⟩;omega
    · exact first_blocker D _ _ (by omega) (by omega)
    · exact z_blocker D _ _ ha (by omega)
  have hq : (D.U-1,D.C-1,D.first.2.2-1) ∈ D.exceptional := by
    apply exceptional_of_blockers D (D.U-1) (D.first.2.2-1) (by omega) (by omega)
    · rintro ⟨_,h⟩;omega
    · exact x_blocker D _ _ hg (by omega)
    · exact first_blocker D _ _ (by omega) (by omega)
  apply two_le_exceptional_of_mem D hp hq
  intro he
  have hx := congrArg Prod.fst he
  change D.first.1-1=D.U-1 at hx
  omega

theorem full_outer_one (D : Data) (ha : 0 < D.first.1) (hg : 0 < D.first.2.2)
    (hout : ¬(D.first.1 < D.U ∧ D.first.2.2 < D.V)) : 1 ≤ D.exceptional.ncard := by
  have hU := D.U_pos;have hV := D.V_pos
  apply one_le_exceptional_of_mem D
  apply exceptional_of_blockers D (D.U-1) (D.V-1) (by omega) (by omega)
  · rintro ⟨hx,hz⟩;apply hout;omega
  · exact x_blocker D _ _ hg (by omega)
  · exact z_blocker D _ _ ha (by omega)

theorem zero_x_one (D : Data) (ha : D.first.1=0) (hg : 0 < D.first.2.2)
    (hgv : D.first.2.2 < D.V) : 1 ≤ D.exceptional.ncard := by
  have hU := D.U_pos;have hV := D.V_pos
  apply one_le_exceptional_of_mem D
  apply exceptional_of_blockers D (D.U-1) (D.first.2.2-1) (by omega) (by omega)
  · rintro ⟨_,h⟩;omega
  · exact x_blocker D _ _ hg (by omega)
  · exact first_blocker D _ _ (by omega) (by omega)

theorem zero_z_one (D : Data) (ha : 0 < D.first.1) (hg : D.first.2.2=0)
    (hau : D.first.1 < D.U) : 1 ≤ D.exceptional.ncard := by
  have hU := D.U_pos;have hV := D.V_pos
  apply one_le_exceptional_of_mem D
  apply exceptional_of_blockers D (D.first.1-1) (D.V-1) (by omega) (by omega)
  · rintro ⟨h,_⟩;omega
  · exact first_blocker D _ _ (by omega) (by omega)
  · exact z_blocker D _ _ ha (by omega)

/-- The arbitrary-original-set cap theorem. All source, wrap and exceptional
sets are constructed; strict/equality caps and unit/zero coordinates are included. -/
theorem compensation (D : Data) :
    D.additionalWraps.ncard + D.fullSupport ≤ D.exceptional.ncard := by
  classical
  rw [additional_wrap_count]
  by_cases hfull : 0 < D.first.1 ∧ 0 < D.first.2.2
  · have hf : D.fullSupport=1 := by simp [Data.fullSupport,hfull]
    rw [hf]
    by_cases hi : D.first.1 < D.U ∧ D.first.2.2 < D.V
    · rw [ite_eq_left hi]
      exact full_inner_two D hfull.1 hfull.2 hi.1 hi.2
    · rw [ite_eq_right hi]
      exact full_outer_one D hfull.1 hfull.2 hi
  · have hf : D.fullSupport=0 := by simp [Data.fullSupport,hfull]
    rw [hf,Nat.add_zero]
    by_cases hi : D.first.1 < D.U ∧ D.first.2.2 < D.V
    · rw [ite_eq_left hi]
      by_cases ha : D.first.1=0
      · have hg : 0 < D.first.2.2 := by have:=D.first_transverse_pos;omega
        exact zero_x_one D ha hg hi.2
      · have hap : 0 < D.first.1 := by omega
        have hg : D.first.2.2=0 := by omega
        exact zero_z_one D hap hg hi.1
    · rw [ite_eq_right hi]
      exact Nat.zero_le _

end NS25Lean.SharedCap
