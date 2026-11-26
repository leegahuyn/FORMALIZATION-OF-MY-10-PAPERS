import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import PrimalitySheafVerification.ManuscriptAudit.NodalBranchLineClassification

/-! The algebraic Picard group of the actual split affine node is the
multiplicative group of its base field. Its global units are constants. -/

namespace ManuscriptAudit.NodalAffinePicard

open Polynomial NodalBranchLines
open NodalBranchLineClassification

noncomputable section
variable (K : Type*) [Field K]

private abbrev S := Submodule (A K) (B K)

private def ratioHom (h2 : (2 : K) ≠ 0) : Kˣ →* (S K)ˣ where
  toFun := branchLineUnit K h2
  map_one' := by
    apply Units.ext
    exact branchLine_one K h2
  map_mul' a b := by
    apply Units.ext
    exact (branchLine_mul K h2 (a : K) (b : K) a.ne_zero).symm

private theorem ratioHom_bijective (h2 : (2 : K) ≠ 0) :
    Function.Bijective (ratioHom K h2) := by
  constructor
  · intro a b h
    apply Units.ext
    apply branchLine_injective K h2
    exact congrArg Units.val h
  · intro I
    obtain ⟨r, hr⟩ := exists_branchLine K h2 I
    exact ⟨r, Units.ext hr.symm⟩

private theorem unitsToPic_injective :
    Function.Injective (Submodule.unitsToPic (A K) (B K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, Submodule.ker_unitsToPic]
  apply bot_unique
  rintro I ⟨v, rfl⟩
  apply Subgroup.mem_bot.mpr
  apply Units.ext
  change Submodule.span (A K) {(v : B K)} = 1
  obtain ⟨a, ha, he⟩ := Polynomial.isUnit_iff.mp v.isUnit
  rw [← he]
  have h : IsUnit (algebraMap K (A K) a) := ha.map (algebraMap K (A K))
  exact Submodule.span_singleton_algebraMap_of_isUnit (A := B K) h

private theorem unitsToPic_surjective :
    Function.Surjective (Submodule.unitsToPic (A K) (B K)) := by
  intro P
  have hp : P ∈ (Submodule.unitsToPic (A K) (B K)).range := by
    rw [Submodule.range_unitsToPic, CommRing.relPic_eq_top]
    exact Subgroup.mem_top _
  exact hp

/-- The actual algebraic Picard group of the split affine node is K×. -/
def picardEquiv (h2 : (2 : K) ≠ 0) : Kˣ ≃* CommRing.Pic (A K) :=
  MulEquiv.ofBijective ((Submodule.unitsToPic (A K) (B K)).comp (ratioHom K h2))
    ⟨(unitsToPic_injective K).comp (ratioHom_bijective K h2).1,
      (unitsToPic_surjective K).comp (ratioHom_bijective K h2).2⟩

/-- Every actual unit of the affine nodal ring is a nonzero constant. -/
def unitsEquiv : Kˣ ≃* (A K)ˣ := by
  refine MulEquiv.ofBijective (Units.map (algebraMap K (A K)).toMonoidHom) ⟨?_, ?_⟩
  · intro a b h
    apply Units.ext
    exact (algebraMap K (A K)).injective (congrArg Units.val h)
  · intro v
    let w : (B K)ˣ := Units.map (algebraMap (A K) (B K)).toMonoidHom v
    obtain ⟨a, ha, he⟩ := Polynomial.isUnit_iff.mp w.isUnit
    refine ⟨ha.unit, ?_⟩
    apply Units.ext
    apply Subtype.ext
    change C (↑ha.unit : K) = (v : A K).val
    rw [IsUnit.unit_spec]
    exact he

/-- The unit term in Kummer degree one is trivial over an algebraically closed
field for every positive exponent. -/
theorem unit_power_surjective [IsAlgClosed K] (d : ℕ) (hd : 0 < d) :
    Function.Surjective (fun u : (A K)ˣ => u ^ d) := by
  intro u
  obtain ⟨a, rfl⟩ := (unitsEquiv K).surjective u
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hd
  have hbn : b ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hb
    exact a.ne_zero hb.symm
  refine ⟨unitsEquiv K (Units.mk0 b hbn), ?_⟩
  rw [← map_pow]
  apply congrArg (unitsEquiv K)
  exact Units.ext hb

end
end ManuscriptAudit.NodalAffinePicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffinePicard.picardEquiv,
      ``ManuscriptAudit.NodalAffinePicard.unitsEquiv,
      ``ManuscriptAudit.NodalAffinePicard.unit_power_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
