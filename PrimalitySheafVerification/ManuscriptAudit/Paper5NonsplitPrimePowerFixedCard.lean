import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitQuarticMultipleCount
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitQuarticIterate
import PrimalitySheafVerification.ManuscriptAudit.PrimePrimaryCardinality

/-! Transfer of exact prime-primary cardinalities from the actual degree-4k finite extension. -/

namespace ManuscriptAudit.Paper5NonsplitPrimePowerFixedCard

open WeierstrassCurve CubicThreeTorsionOrdinate WeierstrassFrobeniusExtensionFixed
open TorsionFrobeniusModule WeierstrassFrobeniusTorsionFixed
open Paper5NonsplitQuarticMultipleCount Paper5NonsplitQuarticIterate PrimePrimaryCardinality

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable (l : ℕ) [Fact l.Prime]

/-- The geometric torsion cardinality is determined by the exact factorization of p^(2k)−1. -/
theorem card_at_exact_factor (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (i : E →ₐ[ZMod p] L) {k : ℕ} (hDegree : Module.finrank (ZMod p) E = 4 * k)
    (n d : ℕ) (hFactor : p ^ (2 * k) - 1 = l ^ n * d) (hd : ¬l ∣ d) :
    Nat.card (Torsion (l ^ n) ((Curve A).baseChange L).Point) = (l ^ 2) ^ n := by
  let W := Curve A
  let H := (W.baseChange E).Point
  let G := (W.baseChange L).Point
  letI : Finite (WithZero {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2}) := by
    change Finite (Option {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2})
    infer_instance
  letI : Finite H := Finite.of_injective _ (Affine.nonsingularPointEquiv (W.baseChange E)).injective
  have hCoeff : p ^ (2 * k) = l ^ n * d + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_iff.mpr (pow_pos (Fact.out : p.Prime).pos _))).symm.trans
      (congrArg (· + 1) hFactor)
  let j : H →+ G := Affine.Point.map (W' := W) i
  have hAnn (P : H) : (l ^ n * d) • P = 0 := by
    have h := (point_iterate_eq_self_iff p L E i W (j P)).mpr ⟨P, rfl⟩
    rw [hDegree, quartic_iterate p L hp hq hA, hCoeff, add_nsmul, one_nsmul] at h
    apply Affine.Point.map_injective (W' := W) i
    rw [map_nsmul, map_zero]
    exact add_right_cancel (h.trans (zero_add (j P)).symm)
  have hCard : Nat.card H = (l ^ n * d) ^ 2 := by
    rw [show Nat.card H = (p ^ (2 * k) - 1) ^ 2 from quartic_multiple_count p hp hq hA hDegree,
      hFactor]
  have hFixed (P : Torsion (l ^ n) G) :
      (frobeniusLinear (l ^ n) p L W ^ Module.finrank (ZMod p) E) P = P := by
    apply inclusion_injective (l ^ n) G
    rw [frobeniusLinear_pow_inclusion, ← point_iterate_eq_map p L W, hDegree,
      quartic_iterate p L hp hq hA, hCoeff, add_nsmul, one_nsmul, mul_nsmul,
      (mem_iff (l ^ n) G _).mp P.property, nsmul_zero, zero_add]
  let e := (rationalTorsionEquiv (l ^ n) p L E i W).trans
    (Equiv.subtypeUnivEquiv hFixed)
  exact (Nat.card_congr e.symm).trans
    (card_torsion_of_square_annihilator H l n d hd hAnn hCard)

end
end ManuscriptAudit.Paper5NonsplitPrimePowerFixedCard

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5NonsplitPrimePowerFixedCard.card_at_exact_factor
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
