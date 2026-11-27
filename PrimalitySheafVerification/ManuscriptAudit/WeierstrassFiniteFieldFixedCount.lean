import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusExtensionFixed

/-! Native geometric fixed points over a general finite base field. -/

namespace ManuscriptAudit.WeierstrassFiniteFieldFixedCount

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNonsplitFrobeniusTrace

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [DecidableEq E] [Field L] [Algebra E L] [DecidableEq L]

theorem pow_card_eq_self_iff (x : L) :
    x ^ Fintype.card E = x ↔ ∃ y : E, algebraMap E L y = x := by
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
    have hRoot : (f.map (algebraMap E L)).IsRoot x := by
      simp [f, Polynomial.IsRoot, hx]
    exact hs.mem_range_of_isRoot hf hRoot
  · rintro ⟨y, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

private abbrev action (W : Affine E) : AddMonoid.End (W.baseChange L).Point :=
  pointMapAt E L W (W.baseChange L) rfl (FiniteField.frobeniusAlgHom E L)

private abbrev inclusion (W : Affine E) :
    (W.baseChange E).Point →+ (W.baseChange L).Point :=
  Affine.Point.map (W' := W) (Algebra.ofId E L)

theorem fixed_iff (W : Affine E) (P : (W.baseChange L).Point) :
    action E L W P = P ↔ ∃ Q : (W.baseChange E).Point, inclusion E L W Q = P := by
  constructor
  · intro h
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y hxy =>
      obtain ⟨h', he⟩ := pointMapAt_some E L W (W.baseChange L) rfl
        (FiniteField.frobeniusAlgHom E L) x y hxy
      have hFixed := Affine.Point.some.inj (he.symm.trans h)
      obtain ⟨a, ha⟩ := (pow_card_eq_self_iff E L x).mp hFixed.1
      obtain ⟨b, hb⟩ := (pow_card_eq_self_iff E L y).mp hFixed.2
      let i := Algebra.ofId E L
      have h₀ : (W.baseChange E).Nonsingular a b :=
        (W.baseChange_nonsingular (f := i) i.injective a b).mp
          (by simpa only [i, Algebra.ofId_apply, ha, hb] using hxy)
      refine ⟨.some a b h₀, ?_⟩
      unfold inclusion
      rw [Affine.Point.map_some]
      simpa only [Algebra.ofId_apply, Affine.Point.some.injEq] using And.intro ha hb
  · rintro ⟨Q, rfl⟩
    change Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom E L)
      (inclusion E L W Q) = inclusion E L W Q
    exact Affine.Point.map_baseChange (W' := W) (FiniteField.frobeniusAlgHom E L) Q

theorem kernel_card (W : Affine E) :
    Nat.card ↥((1 - action E L W).ker) = Nat.card (W.baseChange E).Point := by
  let k := (1 - action E L W).ker
  have hMem (P : (W.baseChange L).Point) : P ∈ k ↔ action E L W P = P := by
    change P - action E L W P = 0 ↔ action E L W P = P
    rw [sub_eq_zero, eq_comm]
  let i (Q : (W.baseChange E).Point) : k :=
    ⟨inclusion E L W Q, (hMem _).mpr ((fixed_iff E L W _).mpr ⟨Q, rfl⟩)⟩
  have hi : Function.Injective i := by
    intro a b h
    exact Affine.Point.map_injective (W' := W) (Algebra.ofId E L) (congrArg Subtype.val h)
  have hs : Function.Surjective i := by
    intro Q
    obtain ⟨P, hP⟩ := (fixed_iff E L W Q.val).mp ((hMem Q.val).mp Q.property)
    exact ⟨P, Subtype.ext hP⟩
  exact Nat.card_congr (Equiv.ofBijective i ⟨hi, hs⟩).symm

variable [IsAlgClosed L]

/-- The fixed subgroup of the native centered Frobenius counts literal projective points. -/
set_option maxHeartbeats 500000 in
theorem centered_kernel_card (A : E) :
    Nat.card ↥((1 - arithmeticPointFrobenius E L A).ker) =
      Nat.card (shortCubic (0 : E) A).toProjective.Point := by
  let W := Curve A
  have hAt {V : Affine L} (hV : W.baseChange L = V) :
      let F : AddMonoid.End V.Point := pointMapAt E L W V hV (FiniteField.frobeniusAlgHom E L)
      Nat.card ↥((1 - F).ker) = Nat.card (W.baseChange E).Point := by
    subst V
    exact kernel_card E L W
  have hSelf : W.baseChange E = W := by rfl
  calc
    _ = Nat.card (W.baseChange E).Point := hAt (centered_baseChange E L A)
    _ = Nat.card W.Point := congrArg (fun w : Affine E => Nat.card w.Point) hSelf
    _ = _ := Nat.card_congr
      (Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : E) A).toProjective)).symm.toEquiv

end
end ManuscriptAudit.WeierstrassFiniteFieldFixedCount

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassFiniteFieldFixedCount.pow_card_eq_self_iff,
      ``ManuscriptAudit.WeierstrassFiniteFieldFixedCount.fixed_iff,
      ``ManuscriptAudit.WeierstrassFiniteFieldFixedCount.kernel_card,
      ``ManuscriptAudit.WeierstrassFiniteFieldFixedCount.centered_kernel_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
