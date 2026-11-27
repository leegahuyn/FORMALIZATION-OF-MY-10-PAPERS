import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitPrimePowerCard
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitExtensionTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace

/-! The native fixed kernels realize the exact arithmetic counts over all split prime-field extensions. -/

namespace ManuscriptAudit.CubicSplitPrimeFixedCounts

open WeierstrassCurve Polynomial FiniteFieldPointCount CubicThreeTorsionOrdinate
open WeierstrassFrobeniusFixed WeierstrassFrobeniusExtensionFixed
open CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open CubicSplitExtensionTraceRecurrence Paper5PrintedRecurrence

noncomputable section

set_option maxHeartbeats 1400000

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L]

/-- The kernel of the n-th actual Frobenius power minus the identity is finite and has the
actual projective point count determined by the covered split-field recurrence. -/
theorem finite_and_card (h₂ : (2 : ZMod p) ≠ 0) (h₃ : (3 : ZMod p) ≠ 0)
    (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) (hn : 0 < n) :
    let F := arithmeticPointFrobenius (ZMod p) L A
    Finite ↥((F ^ n - 1).ker) ∧
      (Nat.card ↥((F ^ n - 1).ker) : ℤ) =
        ((p ^ n : ℕ) : ℤ) + 1 - recurrence p (signedTrace A) n := by
  classical
  let E := GaloisField p n
  letI : Fintype E := Fintype.ofFinite E
  have hDegree : Module.finrank (ZMod p) E = n := GaloisField.finrank p hn.ne'
  letI : Algebra.IsAlgebraic (ZMod p) E := ⟨fun x => ⟨
    (X ^ Fintype.card E - X : (ZMod p)[X]),
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card,
    by simp [FiniteField.pow_card]⟩⟩
  let i : E →ₐ[ZMod p] L := IsAlgClosed.lift
  let W := Curve A
  let H := (W.baseChange E).Point
  let G₀ := (W.baseChange L).Point
  let G := GeometricPoints (ZMod p) L A
  let F := arithmeticPointFrobenius (ZMod p) L A
  let F₀ := frobeniusOnPoints p L W
  let K := (F ^ n - 1).ker
  let e : G₀ ≃+ G := pointTransport L (centered_baseChange (ZMod p) L A)
  change Finite ↥K ∧ (Nat.card ↥K : ℤ) = _
  have hFE (P : G₀) : F (e P) = e (F₀ P) := by
    change e (F₀ (e.symm (e P))) = e (F₀ P)
    rw [e.symm_apply_apply]
  have hPow (j : ℕ) (P : G₀) : (F ^ j) (e P) = e (((⇑F₀)^[j]) P) := by
    induction j with
    | zero =>
        rw [pow_zero, Function.iterate_zero]
        rfl
    | succ j ih =>
        rw [pow_succ']
        change F ((F ^ j) (e P)) = e (((⇑F₀)^[j + 1]) P)
        rw [ih, hFE, Function.iterate_succ_apply']
  let j : H →+ G := e.toAddMonoidHom.comp (Affine.Point.map (W' := W) i)
  have hMem (P : G) : P ∈ K ↔ ∃ Q : H, j Q = P := by
    rw [AddMonoidHom.mem_ker]
    obtain ⟨P₀, rfl⟩ := e.surjective P
    change (F ^ n) (e P₀) - e P₀ = 0 ↔ ∃ Q : H, j Q = e P₀
    rw [sub_eq_zero, hPow]
    have hBase := point_iterate_eq_self_iff p L E i W P₀
    rw [hDegree] at hBase
    constructor
    · intro hp
      obtain ⟨Q, hQ⟩ := hBase.mp (e.injective hp)
      exact ⟨Q, congrArg e hQ⟩
    · rintro ⟨Q, hQ⟩
      exact congrArg e (hBase.mpr ⟨Q, e.injective hQ⟩)
  let jK (Q : H) : K := ⟨j Q, (hMem (j Q)).mpr ⟨Q, rfl⟩⟩
  have hInj : Function.Injective j := e.injective.comp (Affine.Point.map_injective (W' := W) i)
  let eK : H ≃ K := Equiv.ofBijective jK ⟨fun _ _ h => hInj (congrArg Subtype.val h), by
    intro P
    obtain ⟨Q, hQ⟩ := (hMem P.val).mp P.property
    exact ⟨Q, Subtype.ext hQ⟩⟩
  letI : Finite (WithZero {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2}) := by
    change Finite (Option {xy : E × E // (W.baseChange E).Nonsingular xy.1 xy.2})
    infer_instance
  letI : Finite H := Finite.of_injective _ (Affine.nonsingularPointEquiv (W.baseChange E)).injective
  let hProj := Projective.Point.toAffineAddEquiv
    (W := (shortCubic (0 : E) (algebraMap (ZMod p) E A)).toProjective)
  have hCard : Nat.card K =
      Nat.card (shortCubic (0 : E) (algebraMap (ZMod p) E A)).toProjective.Point :=
    (Nat.card_congr eK).symm.trans (Nat.card_congr
      ((pointTransport E (centered_baseChange (ZMod p) E A)).toEquiv.trans hProj.toEquiv.symm))
  refine ⟨Finite.of_injective eK.symm eK.symm.injective, ?_⟩
  have hDiv : 3 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    omega
  have hTrace := extension_trace_eq_recurrence (E := E) h₂ h₃ hA hDiv
  change (Fintype.card E : ℤ) + 1 -
    (Nat.card (shortCubic (0 : E) (algebraMap (ZMod p) E A)).toProjective.Point : ℤ) =
    recurrence (Fintype.card (ZMod p)) (signedTrace A) (Module.finrank (ZMod p) E) at hTrace
  have hCardE := Module.card_eq_pow_finrank (K := ZMod p) (V := E)
  rw [hDegree, ZMod.card] at hCardE
  rw [hCardE, ← hCard, hDegree, ZMod.card] at hTrace
  linarith

end
end ManuscriptAudit.CubicSplitPrimeFixedCounts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitPrimeFixedCounts.finite_and_card
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
