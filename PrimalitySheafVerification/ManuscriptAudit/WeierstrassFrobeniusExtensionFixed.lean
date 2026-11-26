import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoIteration

/-!
# Fixed points of iterated Frobenius over a specified finite extension

The qth-power fixed scalars are the image of the finite field of cardinality q.
Applying this to the two affine coordinates identifies the actual point-group
inclusion with the fixed points of the corresponding iterate.
-/

namespace ManuscriptAudit.WeierstrassFrobeniusExtensionFixed

open Polynomial WeierstrassCurve WeierstrassFrobeniusFixed FrobeniusModTwoIteration

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L]

theorem pow_frobenius_apply (n : ℕ) (x : L) :
    ((FiniteField.frobeniusAlgHom (ZMod p) L) ^ n) x = x ^ (p ^ n) := by
  rw [AlgHom.coe_pow]
  exact scalar_iterate_apply p L n x

section Points

variable [DecidableEq L]

theorem point_iterate_eq_map (W : Affine (ZMod p)) (n : ℕ) (P : (W.baseChange L).Point) :
    ((⇑(frobeniusOnPoints p L W))^[n]) P =
      Affine.Point.map (W' := W) ((FiniteField.frobeniusAlgHom (ZMod p) L) ^ n) P := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    cases P <;> rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobeniusOnPoints, Affine.Point.map_map, pow_succ'] <;>
      rfl

variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E]

/-- Fixed scalars of qth powering are exactly the image of the finite field of cardinality q. -/
theorem pow_card_eq_self_iff (i : E →ₐ[ZMod p] L) (x : L) :
    x ^ Fintype.card E = x ↔ ∃ y : E, i y = x := by
  constructor
  · intro hx
    let f : E[X] := X ^ Fintype.card E - X
    have hf : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E Fintype.one_lt_card
    have hs : f.Splits := by
      rw [splits_iff_card_roots]
      change (X ^ Fintype.card E - X : E[X]).roots.card =
        (X ^ Fintype.card E - X : E[X]).natDegree
      rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq E Fintype.one_lt_card]
    have hRoot : (f.map (i : E →+* L)).IsRoot x := by
      simp [f, Polynomial.IsRoot, hx]
    exact hs.mem_range_of_isRoot hf hRoot
  · rintro ⟨y, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

variable [DecidableEq E]

/-- Fixed points of the corresponding iterate coincide with the actual finite-extension points. -/
theorem point_iterate_eq_self_iff (i : E →ₐ[ZMod p] L) (W : Affine (ZMod p))
    (P : (W.baseChange L).Point) :
    ((⇑(frobeniusOnPoints p L W))^[Module.finrank (ZMod p) E]) P = P ↔
      ∃ Q : (W.baseChange E).Point, Affine.Point.map (W' := W) i Q = P := by
  have hCard := Module.card_eq_pow_finrank (K := ZMod p) (V := E)
  rw [ZMod.card] at hCard
  let f : L →ₐ[ZMod p] L :=
    (FiniteField.frobeniusAlgHom (ZMod p) L) ^ Module.finrank (ZMod p) E
  have hf (x : L) : f x = x ^ Fintype.card E :=
    (pow_frobenius_apply p L _ x).trans (congrArg (fun n : ℕ => x ^ n) hCard.symm)
  rw [point_iterate_eq_map]
  change Affine.Point.map (W' := W) f P = P ↔
    ∃ Q : (W.baseChange E).Point, Affine.Point.map (W' := W) i Q = P
  constructor
  · intro h
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y hxy =>
      rw [Affine.Point.map_some] at h
      have hFixed := Affine.Point.some.inj h
      obtain ⟨a, ha⟩ := (pow_card_eq_self_iff p L E i x).mp
        (by simpa only [hf] using hFixed.1)
      obtain ⟨b, hb⟩ := (pow_card_eq_self_iff p L E i y).mp
        (by simpa only [hf] using hFixed.2)
      have h₀ : (W.baseChange E).Nonsingular a b :=
        (W.baseChange_nonsingular (f := i) i.injective a b).mp
          (by simpa only [ha, hb] using hxy)
      refine ⟨.some a b h₀, ?_⟩
      rw [Affine.Point.map_some]
      simpa only [Affine.Point.some.injEq] using And.intro ha hb
  · rintro ⟨Q, rfl⟩
    have hcomp : f.comp i = i := by
      ext u
      change f (i u) = i u
      rw [hf, ← map_pow, FiniteField.pow_card]
    rw [Affine.Point.map_map, hcomp]

end Points
end
end ManuscriptAudit.WeierstrassFrobeniusExtensionFixed

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionFixed.pow_frobenius_apply,
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionFixed.point_iterate_eq_map,
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionFixed.pow_card_eq_self_iff,
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionFixed.point_iterate_eq_self_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
