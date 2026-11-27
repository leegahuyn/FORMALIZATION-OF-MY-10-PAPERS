import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace

/-! Native scalar powering agrees with repeated point and torsion Frobenius. -/

namespace ManuscriptAudit.WeierstrassNativeFrobeniusPowers

open WeierstrassCurve CubicNonsplitFrobeniusTrace TorsionFrobeniusModule

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

theorem field_frobenius_power_apply [Fintype K] (n : ℕ) (x : L) :
    ((FiniteField.frobeniusAlgHom K L) ^ n) x = x ^ ((Fintype.card K) ^ n) := by
  rw [AlgHom.coe_pow]
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, pow_one]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change (x ^ ((Fintype.card K) ^ n)) ^ Fintype.card K =
        x ^ ((Fintype.card K) ^ (n + 1))
      rw [← pow_mul, pow_succ]

variable [DecidableEq L]

/-- Transported native point maps compose exactly as the scalar endomorphisms do. -/
def pointMapAtMonoidHom (W : Affine K) (V : Affine L) (h : W.baseChange L = V) :
    (L →ₐ[K] L) →* AddMonoid.End V.Point where
  toFun := pointMapAt K L W V h
  map_one' := by
    subst V
    apply AddMonoidHom.ext
    intro P
    change Affine.Point.map (W' := W) (1 : L →ₐ[K] L) P = P
    cases P <;> rfl
  map_mul' := by
    subst V
    intro g f
    apply AddMonoidHom.ext
    intro P
    change Affine.Point.map (W' := W) (g * f) P =
      Affine.Point.map (W' := W) g (Affine.Point.map (W' := W) f P)
    rw [Affine.Point.map_map] <;> rfl

private def torsionMapMonoidHom (m : ℕ) (G : Type*) [AddCommGroup G] :
    AddMonoid.End G →* Module.End (ZMod m) (Torsion m G) where
  toFun := mapLinear m
  map_one' := by
    apply LinearMap.ext
    intro P
    exact Subtype.ext rfl
  map_mul' := by
    intro g f
    apply LinearMap.ext
    intro P
    exact Subtype.ext rfl

/-- A power of the actual map on geometric torsion is induced by the same scalar power. -/
theorem torsion_point_map_pow (m : ℕ) (W : Affine K) (V : Affine L)
    (h : W.baseChange L = V) (g : L →ₐ[K] L) (n : ℕ) :
    mapLinear m (pointMapAt K L W V h g) ^ n =
      mapLinear m (pointMapAt K L W V h (g ^ n)) :=
  (((torsionMapMonoidHom m V.Point).comp (pointMapAtMonoidHom K L W V h)).map_pow g n).symm

end
end ManuscriptAudit.WeierstrassNativeFrobeniusPowers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassNativeFrobeniusPowers.field_frobenius_power_apply,
      ``ManuscriptAudit.WeierstrassNativeFrobeniusPowers.torsion_point_map_pow] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
