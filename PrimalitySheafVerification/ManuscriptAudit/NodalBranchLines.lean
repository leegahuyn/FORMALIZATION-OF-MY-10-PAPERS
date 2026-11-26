import Lean.Util.CollectAxioms
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-! Invertible modules on the split affine node obtained by prescribing
the ratio of the two branch values. -/

namespace ManuscriptAudit.NodalBranchLines

open Polynomial NodalConductor

noncomputable section
variable (K : Type*) [Field K]

abbrev A := coordinates K
abbrev B := Polynomial K

def branchLine (r : K) : Submodule (A K) (B K) where
  carrier := {f | f.eval 1 = r * f.eval (-1)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change f.eval 1 = r * f.eval (-1) at hf
    change g.eval 1 = r * g.eval (-1) at hg
    change (f + g).eval 1 = r * (f + g).eval (-1)
    rw [eval_add, eval_add, hf, hg, mul_add]
  smul_mem' := by
    intro a f hf
    change f.eval 1 = r * f.eval (-1) at hf
    change (a.val * f).eval 1 = r * (a.val * f).eval (-1)
    have ha := (mem_equalBranchValues K a.val).mp (coordinates_le_equalBranchValues K a.property)
    rw [eval_mul, eval_mul, ha, hf]
    ring

theorem mem_branchLine (r : K) (f : B K) :
    f ∈ branchLine K r ↔ f.eval 1 = r * f.eval (-1) := Iff.rfl

def interpolation (a b : K) : B K :=
  C ((a + b) / 2) + C ((a - b) / 2) * X

theorem interpolation_at_one (h2 : (2 : K) ≠ 0) (a b : K) :
    (interpolation K a b).eval 1 = a := by
  simp [interpolation]
  field_simp [h2] <;> ring

theorem interpolation_at_neg_one (h2 : (2 : K) ≠ 0) (a b : K) :
    (interpolation K a b).eval (-1) = b := by
  simp [interpolation]
  field_simp [h2] <;> ring

theorem interpolation_mem (h2 : (2 : K) ≠ 0) (r : K) :
    interpolation K r 1 ∈ branchLine K r := by
  rw [mem_branchLine, interpolation_at_one K h2, interpolation_at_neg_one K h2, mul_one]

theorem conductor_mem_branchLine (r : K) (f : B K) :
    x K * f ∈ branchLine K r := by
  rw [mem_branchLine, eval_mul, eval_mul]
  simp [x]

theorem branchLine_one (h2 : (2 : K) ≠ 0) :
    branchLine K 1 = 1 := by
  ext f
  rw [mem_branchLine, one_mul, Submodule.mem_one]
  constructor
  · intro hf
    refine ⟨⟨f, ?_⟩, rfl⟩
    change f ∈ coordinates K
    rw [coordinates_eq_equalBranchValues K h2, mem_equalBranchValues]
    exact hf
  · rintro ⟨a, rfl⟩
    exact (mem_equalBranchValues K a.val).mp (coordinates_le_equalBranchValues K a.property)

private theorem conductor_mem_product (h2 : (2 : K) ≠ 0) (r s : K) (hr : r ≠ 0) (f : B K) :
    x K * f ∈ branchLine K r * branchLine K s := by
  let p := interpolation K r 1
  let q := interpolation K r⁻¹ 1
  have hp : p ∈ branchLine K r := interpolation_mem K h2 r
  have hdiv : x K ∣ p * q - 1 := by
    rw [x_dvd_iff_vanishes K h2]
    constructor
    · rw [eval_sub, eval_mul, interpolation_at_one K h2, interpolation_at_one K h2,
        eval_one, mul_inv_cancel₀ hr, sub_self]
    · rw [eval_sub, eval_mul, interpolation_at_neg_one K h2, interpolation_at_neg_one K h2,
        eval_one, one_mul, sub_self]
  obtain ⟨g, hg⟩ := hdiv
  have h₁ : p * (x K * (f * q)) ∈ branchLine K r * branchLine K s :=
    Submodule.mul_mem_mul hp (conductor_mem_branchLine K s (f * q))
  have h₂ : x K * (x K * (f * g)) ∈ branchLine K r * branchLine K s :=
    Submodule.mul_mem_mul (by simpa using conductor_mem_branchLine K r 1)
      (conductor_mem_branchLine K s (f * g))
  have h := (branchLine K r * branchLine K s).sub_mem h₁ h₂
  have he : p * (x K * (f * q)) - x K * (x K * (f * g)) = x K * f := by
    calc
      _ = x K * f * (p * q - x K * g) := by ring
      _ = _ := by rw [← hg]; ring
  rwa [he] at h

/-- Multiplication of branch-line submodules multiplies the gluing ratios. -/
theorem branchLine_mul (h2 : (2 : K) ≠ 0) (r s : K) (hr : r ≠ 0) :
    branchLine K r * branchLine K s = branchLine K (r * s) := by
  apply le_antisymm
  · apply Submodule.mul_le.mpr
    intro f hf g hg
    rw [mem_branchLine] at hf hg ⊢
    rw [eval_mul, eval_mul, hf, hg]
    ring
  · intro f hf
    let c := f.eval (-1)
    let p := interpolation K r 1
    let q := interpolation K s 1
    let ac : A K := algebraMap K (A K) c
    have hp : C c * p ∈ branchLine K r :=
      (branchLine K r).smul_mem ac (interpolation_mem K h2 r)
    have hm : C c * p * q ∈ branchLine K r * branchLine K s :=
      Submodule.mul_mem_mul hp (interpolation_mem K h2 s)
    have hdiv : x K ∣ f - C c * p * q := by
      rw [x_dvd_iff_vanishes K h2]
      constructor
      · rw [eval_sub, eval_mul, eval_mul, eval_C,
          interpolation_at_one K h2, interpolation_at_one K h2,
          (mem_branchLine K _ f).mp hf]
        change r * s * c - c * r * s = 0
        ring
      · rw [eval_sub, eval_mul, eval_mul, eval_C,
          interpolation_at_neg_one K h2, interpolation_at_neg_one K h2]
        change c - c * 1 * 1 = 0
        ring
    obtain ⟨g, hg⟩ := hdiv
    have hc : f - C c * p * q ∈ branchLine K r * branchLine K s := by
      rw [hg]
      exact conductor_mem_product K h2 r s hr g
    have h := (branchLine K r * branchLine K s).add_mem hc hm
    rwa [sub_add_cancel] at h

/-- The actual invertible submodule of K[t] with branch ratio r. -/
def branchLineUnit (h2 : (2 : K) ≠ 0) (r : Kˣ) : (Submodule (A K) (B K))ˣ where
  val := branchLine K (r : K)
  inv := branchLine K (↑(r⁻¹) : K)
  val_inv := by rw [branchLine_mul K h2 _ _ r.ne_zero, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    branchLine_one K h2]
  inv_val := by rw [branchLine_mul K h2 _ _ (r⁻¹).ne_zero, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    branchLine_one K h2]

/-- Distinct branch ratios already give distinct submodules. -/
theorem branchLine_injective (h2 : (2 : K) ≠ 0) : Function.Injective (branchLine K) := by
  intro r s he
  have hm : interpolation K r 1 ∈ branchLine K s := he ▸ interpolation_mem K h2 r
  rw [mem_branchLine, interpolation_at_one K h2, interpolation_at_neg_one K h2, mul_one] at hm
  exact hm

end
end ManuscriptAudit.NodalBranchLines

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalBranchLines.branchLine_mul,
      ``ManuscriptAudit.NodalBranchLines.branchLineUnit,
      ``ManuscriptAudit.NodalBranchLines.branchLine_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
