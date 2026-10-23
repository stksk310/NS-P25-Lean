import NS25Lean.P2BranchBPrefixNotchResources

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- A coordinate is chosen from an existing F-value witness, not from a
provenance-uniqueness or active-owner assumption. -/
def nonsymmetricFSourceCoordinate (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricPrefixFSources R hB hQ) : ℕ×ℕ :=
  let ell := Classical.choose s.property.2
  ((nonsymmetricReturnTuple R hB ell).1,(nonsymmetricReturnTuple R hB ell).2.1)

theorem nonsymmetric_F_source_coordinate_spec (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricPrefixFSources R hB hQ) :
    NonsymmetricLDomain R (nonsymmetricFSourceCoordinate R hB hQ s).1
      (nonsymmetricFSourceCoordinate R hB hQ s).2 ∧
    0 < (nonsymmetricFSourceCoordinate R hB hQ s).1 ∧
    0 < (nonsymmetricFSourceCoordinate R hB hQ s).2 ∧
    s.val=(nonsymmetricF R (nonsymmetricFSourceCoordinate R hB hQ s).1
      (nonsymmetricFSourceCoordinate R hB hQ s).2 : ℕ) := by
  have h := nonsymmetricReturnTuple_spec R hB (Classical.choose s.property.2)
  exact ⟨h.1,h.2.1,h.2.2.1,Classical.choose_spec s.property.2⟩

theorem nonsymmetric_F_source_coordinate_return (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricPrefixFSources R hB hQ) :
    ∃ ell : NonsymmetricReturnIndex R,
      ((nonsymmetricReturnTuple R hB ell).1,(nonsymmetricReturnTuple R hB ell).2.1)=
        nonsymmetricFSourceCoordinate R hB hQ s :=
  ⟨Classical.choose s.property.2,rfl⟩

theorem nonsymmetric_F_source_coordinates_unique (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s : NonsymmetricPrefixFSources R hB hQ) {x y : ℕ}
    (hd : NonsymmetricLDomain R x y) (he : s.val=(nonsymmetricF R x y : ℕ)) :
    nonsymmetricFSourceCoordinate R hB hQ s=(x,y) := by
  have hs := nonsymmetric_F_source_coordinate_spec R hB hQ s
  have hn : nonsymmetricF R (nonsymmetricFSourceCoordinate R hB hQ s).1
      (nonsymmetricFSourceCoordinate R hB hQ s).2=nonsymmetricF R x y := by
    exact_mod_cast hs.2.2.2.symm.trans he
  have hc := nonsymmetric_lShape_degree_injective R hs.1 hd (h:=0) (h':=0)
    (by simpa only [zero_mul,zero_add,nonsymmetricF] using hn)
  exact Prod.ext hc.2.1 hc.2.2

theorem nonsymmetricFSourceCoordinate_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricFSourceCoordinate R hB hQ) := by
  intro s t he
  apply Subtype.ext
  rw [(nonsymmetric_F_source_coordinate_spec R hB hQ s).2.2.2,
    (nonsymmetric_F_source_coordinate_spec R hB hQ t).2.2.2,he]

/-- The actual finite coordinate image. Its fields assert only representation,
not antichain, adjacency, or cardinality properties. -/
def NonsymmetricCanonicalFPoints (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  Set.range (nonsymmetricFSourceCoordinate R hB hQ)

def nonsymmetricFCoordinateEquiv (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    NonsymmetricPrefixFSources R hB hQ ≃ NonsymmetricCanonicalFPoints R hB hQ :=
  Equiv.ofInjective _ (nonsymmetricFSourceCoordinate_injective R hB hQ)

theorem nonsymmetric_canonical_F_points_finite (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Finite (NonsymmetricCanonicalFPoints R hB hQ) := by
  letI := nonsymmetric_prefix_F_sources_finite R hB hQ
  exact Finite.of_surjective _ (nonsymmetricFCoordinateEquiv R hB hQ).surjective

theorem nonsymmetric_canonical_F_points_card (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Nat.card (NonsymmetricCanonicalFPoints R hB hQ)=
      Nat.card (NonsymmetricPrefixFSources R hB hQ) :=
  (Nat.card_congr (nonsymmetricFCoordinateEquiv R hB hQ)).symm

private theorem minimal_eq_of_difference {H : NumericalSemigroup} (I : RelativeIdeal H)
    {s t : ℤ} (hs : I.IsMinimalGenerator s) (ht : I.IsMinimalGenerator t)
    (hd : t-s ∈ H.asRelativeIdeal) : s=t := by
  obtain ⟨n,hn,he⟩ := hd
  by_cases h0 : n=0
  · simp only [h0,Nat.cast_zero] at he; omega
  · exact (ht.2 n hn h0 (by convert hs.1 using 1; omega)).elim

theorem nonsymmetric_F_source_antichain (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s t : NonsymmetricPrefixFSources R hB hQ)
    (hx : (nonsymmetricFSourceCoordinate R hB hQ s).1 ≤
      (nonsymmetricFSourceCoordinate R hB hQ t).1)
    (hy : (nonsymmetricFSourceCoordinate R hB hQ s).2 ≤
      (nonsymmetricFSourceCoordinate R hB hQ t).2) : s=t := by
  have hs := nonsymmetric_F_source_coordinate_spec R hB hQ s
  have ht := nonsymmetric_F_source_coordinate_spec R hB hQ t
  apply Subtype.ext
  apply minimal_eq_of_difference _ s.property.1 t.property.1
  rw [hs.2.2.2,ht.2.2.2]
  have hm := nonsymmetric_grid_mem R 0
    ((nonsymmetricFSourceCoordinate R hB hQ t).1-(nonsymmetricFSourceCoordinate R hB hQ s).1)
    ((nonsymmetricFSourceCoordinate R hB hQ t).2-(nonsymmetricFSourceCoordinate R hB hQ s).2)
  convert hm using 1
  simp only [nonsymmetricF,Nat.cast_add,Nat.cast_mul,Nat.cast_zero,zero_mul,zero_add,
    Nat.cast_sub hx,Nat.cast_sub hy]
  ring

theorem nonsymmetric_F_source_x_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (fun s : NonsymmetricPrefixFSources R hB hQ =>
      (nonsymmetricFSourceCoordinate R hB hQ s).1) := by
  intro s t he
  change (nonsymmetricFSourceCoordinate R hB hQ s).1=
    (nonsymmetricFSourceCoordinate R hB hQ t).1 at he
  rcases le_total (nonsymmetricFSourceCoordinate R hB hQ s).2
    (nonsymmetricFSourceCoordinate R hB hQ t).2 with hy | hy
  · exact nonsymmetric_F_source_antichain R hB hQ s t (by omega) hy
  · exact (nonsymmetric_F_source_antichain R hB hQ t s (by omega) hy).symm

theorem nonsymmetric_F_source_y_strict_antitone (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (s t : NonsymmetricPrefixFSources R hB hQ)
    (hx : (nonsymmetricFSourceCoordinate R hB hQ s).1 <
      (nonsymmetricFSourceCoordinate R hB hQ t).1) :
    (nonsymmetricFSourceCoordinate R hB hQ t).2 <
      (nonsymmetricFSourceCoordinate R hB hQ s).2 := by
  by_contra hy
  have he := nonsymmetric_F_source_antichain R hB hQ s t (by omega) (by omega)
  subst t
  omega

private theorem domain_down (R : SectorBCriticalRoleBranchB P) {x y x' y' : ℕ}
    (hd : NonsymmetricLDomain R x' y') (hx : x ≤ x') (hy : y ≤ y') :
    NonsymmetricLDomain R x y := by
  unfold NonsymmetricLDomain at *
  rcases hd.2.2 with h | h
  · exact ⟨by omega,by omega,Or.inl (by omega)⟩
  · exact ⟨by omega,by omega,Or.inr (by omega)⟩

/-- Every actual return has an actual minimal F predecessor. Minimizing the
coordinate sum is a universal well-order argument, not a parameter search. -/
theorem nonsymmetric_return_has_minimal_F_predecessor (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (ell : NonsymmetricReturnIndex R) :
    ∃ s : NonsymmetricPrefixFSources R hB hQ,
      (nonsymmetricFSourceCoordinate R hB hQ s).1 ≤ (nonsymmetricReturnTuple R hB ell).1 ∧
      (nonsymmetricFSourceCoordinate R hB hQ s).2 ≤ (nonsymmetricReturnTuple R hB ell).2.1 := by
  let xy := fun l : NonsymmetricReturnIndex R =>
    ((nonsymmetricReturnTuple R hB l).1,(nonsymmetricReturnTuple R hB l).2.1)
  let E := {l : NonsymmetricReturnIndex R // (xy l).1 ≤ (xy ell).1 ∧ (xy l).2 ≤ (xy ell).2}
  have hne : Nonempty E := ⟨⟨ell,le_refl _,le_refl _⟩⟩
  let f : E → ℕ := fun l => (xy l.val).1+(xy l.val).2
  obtain ⟨k,hk⟩ := natMinImage_spec hne f
  have hmin (l : E) : f k ≤ f l := by rw [hk]; exact natMinImage_le hne f l
  let i := (xy k.val).1
  let j := (xy k.val).2
  have hbnd : i ≤ (xy ell).1 ∧ j ≤ (xy ell).2 := k.property
  have S := nonsymmetricReturnTuple_spec R hB k.val
  have hd : NonsymmetricLDomain R i j := S.1
  have hi : 0 < i := S.2.1
  have hj : 0 < j := S.2.2.1
  have hm : ((nonsymmetricF R i j : ℕ) : ℤ) ∈ nonsymmetricPrefixIdeal R hQ :=
    (nonsymmetric_canonical_prefix_coordinates R hB hQ hd).mpr ⟨k.val,le_refl _,le_refl _⟩
  have hna : ((nonsymmetricF R i j : ℕ) : ℤ)-nsA R ∉ nonsymmetricPrefixIdeal R hQ := by
    intro h
    obtain ⟨l,_,_,hl⟩ := h
    exact nonsymmetric_canonical_a_predecessor_not_mem R hd hl.1
  have hnb : ((nonsymmetricF R i j : ℕ) : ℤ)-nsB R ∉ nonsymmetricPrefixIdeal R hQ := by
    intro h
    have he : ((nonsymmetricF R i j : ℕ) : ℤ)-nsB R=
        ((nonsymmetricF R (i-1) j : ℕ) : ℤ) := by
      have hh : i-1+1=i := by omega
      simp only [nonsymmetricF,Nat.cast_add,Nat.cast_mul]
      have hh' : ((i-1 : ℕ) : ℤ)+1=i := by exact_mod_cast hh
      nlinarith only [hh']
    rw [he] at h
    obtain ⟨l,hli,hlj⟩ := (nonsymmetric_canonical_prefix_coordinates R hB hQ
      (domain_down R hd (by omega : i-1 ≤ i) (le_refl j))).mp h
    let lE : E := ⟨l,by dsimp only [xy] at *; change i ≤ _ ∧ j ≤ _ at hbnd; constructor <;> omega⟩
    have hc := hmin lE
    change i+j ≤ (xy l).1+(xy l).2 at hc
    change (xy l).1 ≤ i-1 at hli
    change (xy l).2 ≤ j at hlj
    omega
  have hnc : ((nonsymmetricF R i j : ℕ) : ℤ)-nsC R ∉ nonsymmetricPrefixIdeal R hQ := by
    intro h
    have he : ((nonsymmetricF R i j : ℕ) : ℤ)-nsC R=
        ((nonsymmetricF R i (j-1) : ℕ) : ℤ) := by
      have hh : j-1+1=j := by omega
      simp only [nonsymmetricF,Nat.cast_add,Nat.cast_mul]
      have hh' : ((j-1 : ℕ) : ℤ)+1=j := by exact_mod_cast hh
      nlinarith only [hh']
    rw [he] at h
    obtain ⟨l,hli,hlj⟩ := (nonsymmetric_canonical_prefix_coordinates R hB hQ
      (domain_down R hd (le_refl i) (by omega : j-1 ≤ j))).mp h
    let lE : E := ⟨l,by dsimp only [xy] at *; change i ≤ _ ∧ j ≤ _ at hbnd; constructor <;> omega⟩
    have hc := hmin lE
    change i+j ≤ (xy l).1+(xy l).2 at hc
    change (xy l).1 ≤ i at hli
    change (xy l).2 ≤ j-1 at hlj
    omega
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  have pos := nonsymmetric_generators_positive R
  have hg := (RelativeIdeal.isMinimalGenerator_iff_sub_generators
    (nonsymmetricPrefixIdeal R hQ) hgen pos.1.ne' pos.2.1.ne' pos.2.2.ne'
    ((nonsymmetricF R i j : ℕ) : ℤ)).mpr ⟨hm,hna,hnb,hnc⟩
  let s : NonsymmetricPrefixFSources R hB hQ := ⟨(nonsymmetricF R i j : ℕ),hg,k.val,rfl⟩
  have hs : nonsymmetricFSourceCoordinate R hB hQ s=(i,j) :=
    nonsymmetric_F_source_coordinates_unique R hB hQ s hd rfl
  refine ⟨s,?_⟩
  rw [hs]
  exact hbnd

theorem nonsymmetric_prefix_CENTER_iff_minimal_F_CENTER (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    (∃ ell : NonsymmetricReturnIndex R,
      (nonsymmetricReturnTuple R hB ell).1 < nsP R ∧
      (nonsymmetricReturnTuple R hB ell).2.1 < nsQ R) ↔
    ∃ s : NonsymmetricPrefixFSources R hB hQ,
      (nonsymmetricFSourceCoordinate R hB hQ s).1 < nsP R ∧
      (nonsymmetricFSourceCoordinate R hB hQ s).2 < nsQ R := by
  constructor
  · rintro ⟨ell,hi,hj⟩
    obtain ⟨s,hsi,hsj⟩ := nonsymmetric_return_has_minimal_F_predecessor R hB hQ ell
    exact ⟨s,lt_of_le_of_lt hsi hi,lt_of_le_of_lt hsj hj⟩
  · rintro ⟨s,hi,hj⟩
    obtain ⟨ell,he⟩ := nonsymmetric_F_source_coordinate_return R hB hQ s
    exact ⟨ell,by simpa only [← he] using hi,by simpa only [← he] using hj⟩

end NS25Lean.L5A2BFinalRepair
