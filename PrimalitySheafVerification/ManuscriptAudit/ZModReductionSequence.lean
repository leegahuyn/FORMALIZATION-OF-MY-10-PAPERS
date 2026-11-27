import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Data.ZMod.Basic

/-! The exact sequence of actual finite cyclic additive groups for divisibility of coefficient orders. -/

namespace ManuscriptAudit.ZModReductionSequence

open CategoryTheory

variable (a b : ℕ)

private def integerMultiples : ℤ →+ ZMod (a * b) where
  toFun x := (a : ZMod (a * b)) * (x : ZMod (a * b))
  map_zero' := by simp
  map_add' := fun x y ↦ by simp [mul_add]

private def killedMultiples : {f : ℤ →+ ZMod (a * b) // f b = 0} :=
  ⟨integerMultiples a b, by
    change (a : ZMod (a * b)) * ((b : ℤ) : ZMod (a * b)) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, ZMod.natCast_self]⟩

/-- Insert the kernel as integer multiples of the target coefficient order. -/
def inclusion : ZMod b →+ ZMod (a * b) :=
  ZMod.lift b (killedMultiples a b)

theorem inclusion_natCast (x : ℕ) :
    inclusion a b (x : ZMod b) = ((a * x : ℕ) : ZMod (a * b)) := by
  have h : inclusion a b ((x : ℤ) : ZMod b) =
      (a : ZMod (a * b)) * ((x : ℤ) : ZMod (a * b)) :=
    ZMod.lift_coe b (killedMultiples a b) (x : ℤ)
  simpa only [Int.cast_natCast, Nat.cast_mul] using h

/-- The actual canonical coefficient reduction homomorphism. -/
def reduction : ZMod (a * b) →+* ZMod a := ZMod.castHom (dvd_mul_right a b) (ZMod a)

theorem reduction_surjective : Function.Surjective (reduction a b) :=
  ZMod.castHom_surjective (dvd_mul_right a b)

variable [NeZero a] [NeZero b]

theorem inclusion_injective : Function.Injective (inclusion a b) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  change inclusion a b x = 0 at hx
  rw [← ZMod.natCast_zmod_val x, inclusion_natCast, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨t, ht⟩ := hx
  have hpos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hVal : x.val = b * t :=
    Nat.eq_of_mul_eq_mul_left hpos (by simpa only [Nat.mul_assoc] using ht)
  change x = (0 : ZMod b)
  rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
  exact ⟨t, hVal⟩

theorem reduction_inclusion (x : ZMod b) : reduction a b (inclusion a b x) = 0 := by
  rw [← ZMod.natCast_zmod_val x, inclusion_natCast, map_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_mul_right a x.val

theorem functionExact : Function.Exact (inclusion a b) (reduction a b) := by
  intro z
  constructor
  · intro hz
    letI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff] at hz
    obtain ⟨t, ht⟩ := hz
    refine ⟨(t : ZMod b), ?_⟩
    rw [inclusion_natCast, ← ht, ZMod.natCast_zmod_val]
  · rintro ⟨t, rfl⟩
    exact reduction_inclusion a b t

/-- The kernel and reduction maps as an actual short complex of abelian groups. -/
def sequence : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (AddCommGrpCat.ofHom (inclusion a b))
    (AddCommGrpCat.ofHom (reduction a b).toAddMonoidHom) (by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact reduction_inclusion a b)

theorem sequence_shortExact : (sequence a b).ShortExact :=
  ShortComplex.ShortExact.mk'
    ((ShortComplex.ab_exact_iff_function_exact _).mpr (functionExact a b))
    ((AddCommGrpCat.mono_iff_injective _).mpr (inclusion_injective a b))
    ((AddCommGrpCat.epi_iff_surjective _).mpr (reduction_surjective a b))

end ManuscriptAudit.ZModReductionSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ZModReductionSequence.inclusion_natCast,
      ``ManuscriptAudit.ZModReductionSequence.inclusion_injective,
      ``ManuscriptAudit.ZModReductionSequence.reduction_surjective,
      ``ManuscriptAudit.ZModReductionSequence.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
