import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Localization.Defs

/-! A surjective flat ring map is a localization at the elements mapping
to one. The explicit denominator can be lifted across a quotient. -/

namespace ManuscriptAudit.FlatSurjectionLocalization

open scoped BigOperators

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

def oneFiber : Submonoid R where
  carrier := {x | algebraMap R S x = 1}
  one_mem' := map_one _
  mul_mem' := by
    intro x y hx hy
    change algebraMap R S x = 1 at hx
    change algebraMap R S y = 1 at hy
    change algebraMap R S (x * y) = 1
    rw [map_mul, hx, hy, mul_one]

variable {R S}

/-- A zero in the flat quotient is killed by a denominator with image one. -/
theorem exists_annihilator [Module.Flat R S]
    (hs : Function.Surjective (algebraMap R S)) (a : R)
    (ha : algebraMap R S a = 0) : ∃ u : oneFiber R S, (u : R) * a = 0 := by
  classical
  let f : Fin 1 → R := fun _ ↦ a
  let x : Fin 1 → S := fun _ ↦ 1
  have hr : ∑ i, f i • x i = 0 := by
    simpa [f, x, Algebra.smul_def] using ha
  obtain ⟨k, b, y, he, hz⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hr
  choose z hzs using fun j ↦ hs (y j)
  let t : R := ∑ j, b 0 j * z j
  have ht : algebraMap R S t = 1 := by
    calc
      algebraMap R S t = ∑ j, b 0 j • y j := by
        dsimp only [t]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul, hzs, Algebra.smul_def]
      _ = 1 := (he 0).symm
  refine ⟨⟨t, ht⟩, ?_⟩
  change t * a = 0
  rw [mul_comm t a, show t = ∑ j, b 0 j * z j by rfl, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hj : a * b 0 j = 0 := by simpa [f] using hz j
  rw [← mul_assoc, hj, zero_mul]

/-- The actual ring map exhibits a localization, without finite presentation. -/
theorem isLocalization [Module.Flat R S]
    (hs : Function.Surjective (algebraMap R S)) :
    IsLocalization (oneFiber R S) S := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change IsUnit (algebraMap R S (x : R))
    rw [show algebraMap R S (x : R) = 1 from x.property]
    exact isUnit_one
  · intro z
    obtain ⟨x, hx⟩ := hs z
    refine ⟨(x, 1), ?_⟩
    change z * algebraMap R S 1 = algebraMap R S x
    rw [map_one, mul_one, hx]
  · intro x y h
    obtain ⟨t, ht⟩ := exists_annihilator hs (x - y) (by rw [map_sub, h, sub_self])
    exact ⟨t, sub_eq_zero.mp (by simpa only [mul_sub] using ht)⟩

end ManuscriptAudit.FlatSurjectionLocalization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FlatSurjectionLocalization.isLocalization
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
