import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CuspCotangent
import PrimalitySheafVerification.Spt3

/-!
# Paper 3, Theorem 20, on actual affine fibers and derived overlap Tor

With p = 5 and k = 1 the unit modulus gives zero derived Tor on a
singular cusp fiber whose first cotangent homology is zero. The
modulus 5 gives nonzero derived Tor on a smooth affine line fiber.
The second instance concerns a fixed modulus, as in the displayed
overlap, when that modulus is permitted in the test.
-/

namespace ManuscriptAudit.Paper3OverlapCotangent

open CategoryTheory

noncomputable section

abbrev derivedOverlap (M N : ℕ) :=
  (Spt3Tor.Tor (ModuleCat.of ℤ (ZMod M)) 1).obj (ModuleCat.of ℤ (ZMod N))

theorem unit_modulus_tor_is_zero :
    Subsingleton (derivedOverlap 1 5) := by
  let e := (Spt3TorValue.tor1_obj_iso 1 5).toLinearEquiv
  have h : Nat.gcd 1 5 = 1 := by decide
  letI : Subsingleton (ModuleCat.of ℤ (ZMod (Nat.gcd 1 5))) := by
    change Subsingleton (ZMod (Nat.gcd 1 5))
    rw [h]
    infer_instance
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

theorem five_modulus_tor_is_nonzero :
    ¬ Subsingleton (derivedOverlap 5 5) := by
  let e := (Spt3TorValue.tor1_obj_iso 5 5).toLinearEquiv
  intro h
  have hx : e.symm 0 = e.symm 1 := h.allEq _ _
  have hy : (0 : ZMod (Nat.gcd 5 5)) = 1 := e.symm.injective hx
  rw [Nat.gcd_self] at hy
  exact (by decide : (0 : ZMod 5) ≠ 1) hy

/-- The vanishing of the two displayed obstruction groups need not imply smoothness. -/
theorem zero_tor_and_zero_cotangent_on_singular_cusp :
    Subsingleton (derivedOverlap 1 5) ∧
    Subsingleton (Algebra.H1Cotangent (ZMod 5) (CuspCotangent.CuspRing (ZMod 5))) ∧
    ¬ Algebra.Smooth (ZMod 5) (CuspCotangent.CuspRing (ZMod 5)) := by
  exact ⟨unit_modulus_tor_is_zero,
    CuspCotangent.paper2_integral_cusp_h1_cotangent_vanishing_and_singular _ (by decide)⟩

/-- Smoothness and zero cotangent homology need not imply zero Tor for the fixed overlap. -/
theorem smooth_line_with_nonzero_tor :
    Algebra.Smooth (ZMod 5) (Polynomial (ZMod 5)) ∧
    Subsingleton (Algebra.H1Cotangent (ZMod 5) (Polynomial (ZMod 5))) ∧
    ¬ Subsingleton (derivedOverlap 5 5) := by
  letI : Algebra.Smooth (ZMod 5) (Polynomial (ZMod 5)) := ⟨inferInstance, inferInstance⟩
  exact ⟨inferInstance, Algebra.FormallySmooth.subsingleton_h1Cotangent,
    five_modulus_tor_is_nonzero⟩

end

end ManuscriptAudit.Paper3OverlapCotangent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper3OverlapCotangent.unit_modulus_tor_is_zero,
      ``ManuscriptAudit.Paper3OverlapCotangent.five_modulus_tor_is_nonzero,
      ``ManuscriptAudit.Paper3OverlapCotangent.zero_tor_and_zero_cotangent_on_singular_cusp,
      ``ManuscriptAudit.Paper3OverlapCotangent.smooth_line_with_nonzero_tor] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
