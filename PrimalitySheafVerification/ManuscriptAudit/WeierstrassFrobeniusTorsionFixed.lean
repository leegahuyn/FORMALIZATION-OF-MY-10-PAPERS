import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! The fixed points of actual iterated Frobenius on native torsion are rational torsion. -/

namespace ManuscriptAudit.WeierstrassFrobeniusTorsionFixed

open WeierstrassCurve WeierstrassFrobeniusFixed WeierstrassFrobeniusExtensionFixed
open TorsionFrobeniusModule

noncomputable section

variable (m p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [DecidableEq E]
variable (i : E →ₐ[ZMod p] L) (W : Affine (ZMod p))

abbrev FixedTorsion :=
  {P : geometricTorsion m p L W //
    (frobeniusLinear m p L W ^ Module.finrank (ZMod p) E) P = P}

/-- Torsion-valued fixed point descent for an actual finite-field embedding. -/
theorem fixed_iff_rational (P : geometricTorsion m p L W) :
    (frobeniusLinear m p L W ^ Module.finrank (ZMod p) E) P = P ↔
      ∃ Q : Torsion m (W.baseChange E).Point, pointMap m W i Q = P := by
  let k := Module.finrank (ZMod p) E
  let v := inclusion m _ P
  have hpower : inclusion m _ ((frobeniusLinear m p L W ^ k) P) =
      ((⇑(frobeniusOnPoints p L W))^[k]) v := by
    rw [point_iterate_eq_map p L W k v]
    exact frobeniusLinear_pow_inclusion m p L W k P
  have hFixed : ((⇑(frobeniusOnPoints p L W))^[k]) v = v ↔
      ∃ Q : (W.baseChange E).Point, Affine.Point.map (W' := W) i Q = v :=
    point_iterate_eq_self_iff p L E i W v
  constructor
  · intro hF
    have hfix : ((⇑(frobeniusOnPoints p L W))^[k]) v = v :=
      hpower.symm.trans (congrArg (inclusion m _) hF)
    obtain ⟨Q, hQ⟩ := hFixed.mp hfix
    have hT : m • Q = 0 := by
      apply Affine.Point.map_injective (W' := W) i
      rw [map_nsmul, map_zero, hQ]
      exact (mem_iff m _ _).mp P.property
    refine ⟨⟨Q, (mem_iff m _ _).mpr hT⟩, Subtype.ext ?_⟩
    exact hQ
  · rintro ⟨Q, hQ⟩
    have hq : Affine.Point.map (W' := W) i (Q : (W.baseChange E).Point) = v :=
      congrArg (inclusion m _) hQ
    exact inclusion_injective m _ (hpower.trans (hFixed.mpr ⟨Q, hq⟩))

/-- The actual fixed torsion points are equivalent to the actual finite-extension torsion. -/
def rationalTorsionEquiv :
    Torsion m (W.baseChange E).Point ≃ FixedTorsion m p L E W :=
  Equiv.ofBijective (fun P => ⟨pointMap m W i P,
    (fixed_iff_rational m p L E i W _).mpr ⟨P, rfl⟩⟩) (by
    constructor
    · intro a b h
      exact pointMap_injective m W i (congrArg Subtype.val h)
    · intro y
      obtain ⟨P, hP⟩ := (fixed_iff_rational m p L E i W y.val).mp y.property
      exact ⟨P, Subtype.ext hP⟩)

end
end ManuscriptAudit.WeierstrassFrobeniusTorsionFixed

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassFrobeniusTorsionFixed.fixed_iff_rational,
      ``ManuscriptAudit.WeierstrassFrobeniusTorsionFixed.rationalTorsionEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
