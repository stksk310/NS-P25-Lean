import NS25Lean.AttainedCapCompensation

set_option autoImplicit false
noncomputable section
namespace NS25Lean.SharedCap.BoundaryChecks

def unitO : Set Monomial := {(2,0,0),(0,0,2),(1,1,1),(1,1,0),(0,1,1)}

theorem unit_zero_iff (i k : ℕ) :
    (i,0,k) ∈ Closure (ZeroGenerators unitO) ↔ 2 ≤ i ∨ 2 ≤ k := by
  constructor
  · rintro ⟨g,hg,hd⟩
    have ho:=hg.1
    simp only [unitO,Set.mem_insert_iff,Set.mem_singleton_iff] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hd.1
    · exact Or.inr hd.2.2
    · norm_num [ZeroGenerators] at hg
    · norm_num [ZeroGenerators] at hg
    · norm_num [ZeroGenerators] at hg
  · rintro (hi | hk)
    · exact ⟨(2,0,0),⟨by simp [unitO],rfl⟩,hi,le_rfl,Nat.zero_le _⟩
    · exact ⟨(0,0,2),⟨by simp [unitO],rfl⟩,Nat.zero_le _,le_rfl,hk⟩

/-- Both caps are attained at unit width and the first coordinates equal the caps. -/
def unitData : Data where
  C:=2
  u:=1
  v:=1
  U:=1
  V:=1
  C_pos:=by decide
  u_pos:=by decide
  v_pos:=by decide
  U_pos:=by decide
  V_pos:=by decide
  originals:=unitO
  originals_finite:=by simp [unitO]
  first:=(1,1,1)
  first_mem:=by simp [unitO]
  first_y_pos:=by decide
  first_transverse_pos:=by decide
  normal:=by
    intro g hg
    simp only [unitO,Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide
  shape:=by
    intro g hg hne hy
    simp only [unitO,Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · norm_num at hy
    · norm_num at hy
    · exact (hne rfl).elim
    · exact Or.inl ⟨le_rfl,rfl⟩
    · exact Or.inr ⟨le_rfl,rfl⟩
  other_wraps:=by
    intro g hg hne hy
    simp only [unitO,Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · norm_num at hy
    · norm_num at hy
    · exact (hne rfl).elim
    · exact (unit_zero_iff 2 1).mpr (Or.inl le_rfl)
    · exact (unit_zero_iff 1 2).mpr (Or.inr le_rfl)
  rectangle:=by
    intro i k hi hk hh
    rcases (unit_zero_iff i k).mp hh with h | h <;> omega
  central:=by
    intro i k hi hk
    rw [unit_zero_iff]
    omega
  attained_x:=by
    intro _
    exact ⟨(1,1,0),by simp [unitO],by decide,rfl,by decide,rfl⟩
  attained_z:=by
    intro _
    exact ⟨(0,1,1),by simp [unitO],by decide,rfl,by decide,rfl⟩

theorem unit_exceptional : unitData.exceptional={(0,1,0)} := by
  apply Set.Subset.antisymm
  · rintro ⟨x,y,z⟩ hp
    have hb:=exceptional_transverse_bounds unitData hp
    change x<1 ∧ z<1 at hb
    have hy : y+1=2 := hp.2.1
    have hx0 : x=0 := by omega
    have hz0 : z=0 := by omega
    have hy1 : y=1 := by omega
    simp [hx0,hy1,hz0]
  · rintro p rfl
    apply exceptional_of_blockers unitData 0 0 (by decide) (by decide)
    · change ¬(1 ≤ 0 ∧ 1 ≤ 0);decide
    · exact x_blocker unitData 1 0 (by decide) le_rfl
    · exact z_blocker unitData 0 1 (by decide) le_rfl

example : unitData.additionalWraps.ncard=0 := by
  rw [additional_wrap_count]
  decide
example : unitData.fullSupport=1 := by rfl
example : unitData.exceptional.ncard=1 := by rw [unit_exceptional];simp
example : unitData.additionalWraps.ncard+unitData.fullSupport ≤ unitData.exceptional.ncard :=
  compensation unitData

#print axioms unit_exceptional
#print axioms unitData
end NS25Lean.SharedCap.BoundaryChecks
