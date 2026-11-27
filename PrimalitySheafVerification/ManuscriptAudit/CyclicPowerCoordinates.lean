import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! A surjection between cyclic prime-power groups permits compatible coordinates on the larger group. -/

namespace ManuscriptAudit.CyclicPowerCoordinates

noncomputable section

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

private abbrev reduce (r : ℕ) :=
  PadicResidueSystems.reduction ℓ (Nat.le_succ r)

private def scaleByUnit {R : Type*} [CommRing R] (u : Rˣ) : R ≃+ R where
  toFun x := (u : R) * x
  invFun x := ((u⁻¹ : Rˣ) : R) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ x y

private theorem map_eq_mul_reduce (r : ℕ)
    (f : ZMod (ℓ ^ (r + 1)) →+ ZMod (ℓ ^ r)) (x : ZMod (ℓ ^ (r + 1))) :
    f x = f 1 * reduce ℓ r x := by
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  have ha : (a : ZMod (ℓ ^ (r + 1))) = a • (1 : ZMod (ℓ ^ (r + 1))) := by
    rw [nsmul_eq_mul, mul_one]
  calc
    f (a : ZMod (ℓ ^ (r + 1))) = f (a • (1 : ZMod (ℓ ^ (r + 1)))) := congrArg f ha
    _ = a • f 1 := map_nsmul f _ _
    _ = f 1 * reduce ℓ r (a : ZMod (ℓ ^ (r + 1))) := by
      rw [nsmul_eq_mul, map_natCast, mul_comm]

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- For any chosen coordinates on the lower level, one can adjust coordinates
on the upper level so that the actual surjection becomes canonical reduction. -/
def compatibleLift (r : ℕ) (f : B →+ A) (hf : Function.Surjective f)
    (lower : A ≃+ ZMod (ℓ ^ r)) (upper : B ≃+ ZMod (ℓ ^ (r + 1))) :
    {e : B ≃+ ZMod (ℓ ^ (r + 1)) // ∀ x, reduce ℓ r (e x) = lower (f x)} := by
  cases r with
  | zero =>
    letI : Subsingleton (ZMod (ℓ ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
    exact ⟨upper, fun _ ↦ Subsingleton.elim _ _⟩
  | succ r =>
    let F := lower.toAddMonoidHom.comp (f.comp upper.symm.toAddMonoidHom)
    have hF : Function.Surjective F := lower.surjective.comp (hf.comp upper.symm.surjective)
    let u := F 1
    have hu : IsUnit u := by
      obtain ⟨x, hx⟩ := hF 1
      exact isUnit_iff_exists_inv.mpr ⟨reduce ℓ (r + 1) x,
        (map_eq_mul_reduce ℓ (r + 1) F x).symm.trans hx⟩
    let k := u.val
    have hk : (k : ZMod (ℓ ^ (r + 1))) = u := ZMod.natCast_zmod_val u
    have hlo : IsUnit (k : ZMod (ℓ ^ (r + 1))) := by rwa [hk]
    have hprime : ℓ.Prime := Fact.out
    have hnd : ¬ ℓ ∣ k := (ZMod.isUnit_natCast_iff_not_dvd_pow hprime (Nat.succ_pos r)).mp hlo
    have hup : IsUnit (k : ZMod (ℓ ^ (r + 1 + 1))) :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow hprime (Nat.succ_pos (r + 1))).mpr hnd
    let v := hup.unit
    have hv : reduce ℓ (r + 1) (v : ZMod (ℓ ^ (r + 1 + 1))) = u := by
      rw [show (v : ZMod (ℓ ^ (r + 1 + 1))) = (k : ZMod (ℓ ^ (r + 1 + 1))) from hup.unit_spec,
        map_natCast, hk]
    refine ⟨upper.trans (scaleByUnit v), fun x ↦ ?_⟩
    change reduce ℓ (r + 1) ((v : ZMod (ℓ ^ (r + 1 + 1))) * upper x) = lower (f x)
    rw [map_mul, hv]
    calc
      _ = F (upper x) := (map_eq_mul_reduce ℓ (r + 1) F (upper x)).symm
      _ = lower (f x) := by
        change lower (f (upper.symm (upper x))) = lower (f x)
        rw [upper.symm_apply_apply]

end
end ManuscriptAudit.CyclicPowerCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CyclicPowerCoordinates.compatibleLift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
