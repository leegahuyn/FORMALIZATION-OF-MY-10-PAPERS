import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalBranchLines

/-! Every invertible submodule of the normalization comes from one
and only one nonzero ratio of the two branch values. -/

namespace ManuscriptAudit.NodalBranchLineClassification

open Polynomial NodalConductor NodalBranchLines

noncomputable section
variable (K : Type*) [Field K]

private abbrev S := Submodule (A K) (B K)

private theorem unit_one_mem_mul (I : (S K)ˣ) :
    (1 : B K) ∈ I.val * (I⁻¹).val := by
  change (1 : B K) ∈ (↑(I * I⁻¹) : S K)
  rw [mul_inv_cancel]
  exact (map_one (algebraMap (A K) (B K))) ▸ Submodule.algebraMap_mem (1 : A K)

private theorem unit_has_nonzero_value (I : (S K)ˣ) (a : K) :
    ∃ f ∈ I.val, f.eval a ≠ 0 := by
  by_contra h
  have hzero (f : B K) (hf : f ∈ I.val) : f.eval a = 0 :=
    not_ne_iff.mp (fun hne => h ⟨f, hf, hne⟩)
  have h₁ : (1 : B K).eval a = 0 :=
    Submodule.mul_induction_on (C := fun p : B K => p.eval a = 0) (unit_one_mem_mul K I)
      (fun f hf g _ => by rw [eval_mul, hzero f hf, zero_mul])
      (fun f g hf hg => by rw [eval_add, hf, hg, zero_add])
  exact one_ne_zero (by simpa only [eval_one] using h₁ : (1 : K) = 0)

private theorem C_mul_mem (I : S K) (a : K) {f : B K} (hf : f ∈ I) :
    C a * f ∈ I :=
  I.smul_mem (algebraMap K (A K) a) hf

private theorem unit_conductor_mem (I : (S K)ˣ) (b : B K) :
    x K * b ∈ I.val := by
  have h : x K * b * (1 : B K) ∈ I.val := by
    refine Submodule.mul_induction_on (C := fun p : B K => x K * b * p ∈ I.val)
      (unit_one_mem_mul K I) ?_ ?_
    · intro f hf g _
      let a : A K := ⟨x K * (b * g), x_mul_mem_coordinates K (b * g)⟩
      have ha := I.val.smul_mem a hf
      change (x K * (b * g)) * f ∈ I.val at ha
      convert ha using 1 <;> ring
    · intro f g hf hg
      rw [mul_add]
      exact I.val.add_mem hf hg
  simpa only [mul_one] using h

private theorem unit_mem_of_matching_values (h2 : (2 : K) ≠ 0) (I : (S K)ˣ) {f g : B K}
    (hg : g ∈ I.val) (hpos : f.eval 1 = g.eval 1) (hneg : f.eval (-1) = g.eval (-1)) :
    f ∈ I.val := by
  have hd : x K ∣ f - g := by
    rw [x_dvd_iff_vanishes K h2]
    exact ⟨by rw [eval_sub, hpos, sub_self], by rw [eval_sub, hneg, sub_self]⟩
  obtain ⟨b, hb⟩ := hd
  have hm : f - g ∈ I.val := by
    rw [hb]
    exact unit_conductor_mem K I b
  have hf := I.val.add_mem hm hg
  rwa [sub_add_cancel] at hf

private theorem membership_one_equal_values {f : B K} (h : f ∈ (1 : S K)) :
    f.eval 1 = f.eval (-1) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp h
  exact (mem_equalBranchValues K a.val).mp (coordinates_le_equalBranchValues K a.property)

private theorem unit_ne_top (h2 : (2 : K) ≠ 0) (I : (S K)ˣ) : I.val ≠ ⊤ := by
  intro hI
  obtain ⟨g, hg, hgneg⟩ := unit_has_nonzero_value K I⁻¹ (-1)
  have hmul {f : B K} (hf : f ∈ I.val) : f * g ∈ (1 : S K) := by
    have h : f * g ∈ I.val * (I⁻¹).val := Submodule.mul_mem_mul hf hg
    change f * g ∈ (↑(I * I⁻¹) : S K) at h
    rwa [mul_inv_cancel] at h
  have hg' : g ∈ (1 : S K) := by
    simpa only [one_mul] using hmul (f := 1) (by rw [hI]; exact Submodule.mem_top)
  have hXg : Polynomial.X * g ∈ (1 : S K) :=
    hmul (by rw [hI]; exact Submodule.mem_top)
  have h := membership_one_equal_values K hXg
  rw [eval_mul, eval_mul, eval_X, eval_X, one_mul, membership_one_equal_values K hg'] at h
  have hzero : (2 : K) * g.eval (-1) = 0 := by
    calc
      _ = g.eval (-1) - (-1) * g.eval (-1) := by ring
      _ = 0 := sub_eq_zero.mpr h
  exact hgneg ((mul_eq_zero.mp hzero).resolve_left h2)

/-- All invertible submodules of the normalization are actual branch-ratio lines. -/
theorem exists_branchLine (h2 : (2 : K) ≠ 0) (I : (S K)ˣ) :
    ∃ r : Kˣ, I.val = branchLine K r := by
  obtain ⟨v, hv, hvneg⟩ := unit_has_nonzero_value K I (-1)
  let r : K := v.eval 1 / v.eval (-1)
  have hvpos : v.eval 1 = r * v.eval (-1) := (div_mul_cancel₀ _ hvneg).symm
  have hgraph : I.val ≤ branchLine K r := by
    intro f hf
    rw [mem_branchLine]
    by_contra hbad
    let c := f.eval (-1) / v.eval (-1)
    let q := f - C c * v
    have hq : q ∈ I.val := I.val.sub_mem hf (C_mul_mem K I.val c hv)
    have hqneg : q.eval (-1) = 0 := by
      change (f - C c * v).eval (-1) = 0
      rw [eval_sub, eval_mul, eval_C, div_mul_cancel₀ _ hvneg, sub_self]
    have hqpos : q.eval 1 ≠ 0 := by
      intro hz
      change (f - C c * v).eval 1 = 0 at hz
      rw [eval_sub, eval_mul, eval_C, sub_eq_zero] at hz
      apply hbad
      calc
        f.eval 1 = c * v.eval 1 := hz
        _ = r * (c * v.eval (-1)) := by rw [hvpos]; ring
        _ = r * f.eval (-1) := by rw [div_mul_cancel₀ _ hvneg]
    apply unit_ne_top K h2 I
    apply top_unique
    intro z _
    let d := z.eval (-1) / v.eval (-1)
    let e := (z.eval 1 - d * v.eval 1) / q.eval 1
    let w := C d * v + C e * q
    have hw : w ∈ I.val := I.val.add_mem (C_mul_mem K I.val d hv) (C_mul_mem K I.val e hq)
    apply unit_mem_of_matching_values K h2 I hw
    · change z.eval 1 = (C d * v + C e * q).eval 1
      rw [eval_add, eval_mul, eval_mul, eval_C, eval_C, div_mul_cancel₀ _ hqpos]
      ring
    · change z.eval (-1) = (C d * v + C e * q).eval (-1)
      rw [eval_add, eval_mul, eval_mul, eval_C, eval_C, hqneg, mul_zero, add_zero,
        div_mul_cancel₀ _ hvneg]
  have hr : r ≠ 0 := by
    intro h
    obtain ⟨f, hf, hpos⟩ := unit_has_nonzero_value K I 1
    exact hpos (by simpa only [h, zero_mul] using (mem_branchLine K r f).mp (hgraph hf))
  refine ⟨Units.mk0 r hr, le_antisymm hgraph ?_⟩
  intro f hf
  let c := f.eval (-1) / v.eval (-1)
  apply unit_mem_of_matching_values K h2 I (C_mul_mem K I.val c hv)
  · rw [eval_mul, eval_C, hvpos]
    calc
      f.eval 1 = r * f.eval (-1) := (mem_branchLine K r f).mp hf
      _ = r * (c * v.eval (-1)) := by rw [div_mul_cancel₀ _ hvneg]
      _ = _ := by ring
  · rw [eval_mul, eval_C, div_mul_cancel₀ _ hvneg]

end
end ManuscriptAudit.NodalBranchLineClassification

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalBranchLineClassification.exists_branchLine
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
