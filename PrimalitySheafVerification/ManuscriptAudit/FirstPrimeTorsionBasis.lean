import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Cardinality
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! The cardinality l² gives a genuine basis of first-level l-torsion. -/

namespace ManuscriptAudit.FirstPrimeTorsionBasis

open PowerTorsionTower

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]

def basis (hCard : Nat.card (PowerTorsion l G 1) = l ^ 2) :
    Module.Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1) := by
  let V := PowerTorsion l G 1
  let R := ZMod (l ^ 1)
  have hl : l.Prime := Fact.out
  letI : Fact (Nat.Prime (l ^ 1)) := ⟨by simpa only [pow_one] using hl⟩
  letI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [show Nat.card V = l ^ 2 from hCard]
    exact pow_ne_zero 2 hl.ne_zero)
  letI : Fintype V := Fintype.ofFinite V
  letI : Module.Finite R V := Module.Finite.of_finite
  have hR : Fintype.card R = l := (ZMod.card (l ^ 1)).trans (pow_one l)
  have hPow : l ^ Module.finrank R V = l ^ 2 := by
    calc
      _ = (Fintype.card R) ^ Module.finrank R V :=
        congrArg (fun q : ℕ => q ^ Module.finrank R V) hR.symm
      _ = Fintype.card V := (Module.card_eq_pow_finrank (K := R) (V := V)).symm
      _ = _ := (Nat.card_eq_fintype_card (α := V)).symm.trans hCard
  have hDim : Module.finrank R V = 2 := pow_right_injective₀ hl.pos hl.ne_one hPow
  exact (Module.finBasis R V).reindex (finCongr hDim)

end
end ManuscriptAudit.FirstPrimeTorsionBasis

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FirstPrimeTorsionBasis.basis
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
