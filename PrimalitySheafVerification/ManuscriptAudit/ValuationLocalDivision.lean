import Lean.Util.CollectAxioms
import Mathlib.Algebra.Regular.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-! At a local map from a valuation ring, one can detect absence of a
pole from a division equation with regular denominator in the target. -/

namespace ManuscriptAudit.ValuationLocalDivision

variable {D T : Type*} [CommRing D] [CommRing T] [IsDomain D] [ValuationRing D]

/-- If the image of a denominator is regular, a division equation in
the local target already has its quotient in the source valuation ring. -/
theorem exists_quotient (f : D →+* T) [IsLocalHom f] {a b : D} {z : T}
    (hb : IsRegular (f b)) (h : f a = f b * z) :
    ∃ q : D, b * q = a ∧ f q = z := by
  have hd : b ∣ a := by
    rcases ValuationRing.dvd_total b a with hd | ⟨c, hc⟩
    · exact hd
    · have hc' : f b = f a * f c := by rw [hc, map_mul]
      have ha : IsRegular (f a) := IsRegular.of_mul_left (hc' ▸ hb)
      have hu : f c * z = 1 := ha.left (by
        calc
          f a * (f c * z) = f b * z := by rw [← mul_assoc, ← hc']
          _ = f a * 1 := by rw [← h, mul_one])
      have hu' : IsUnit (f c) := ⟨⟨f c, z, hu, by rw [mul_comm, hu]⟩, rfl⟩
      have huc : IsUnit c := (isUnit_map_iff f c).mp hu'
      obtain ⟨u, hu⟩ := huc
      refine ⟨↑u⁻¹, ?_⟩
      rw [hc, ← hu, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨q, hq⟩ := hd
  refine ⟨q, hq.symm, hb.left ?_⟩
  rw [← map_mul, ← hq, h]

end ManuscriptAudit.ValuationLocalDivision

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ValuationLocalDivision.exists_quotient
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
