import Lean.Util.CollectAxioms
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-! The two displayed affine charts of the integral plane node and the
actual transition isomorphism on their overlap, over any coefficient ring. -/

namespace ManuscriptAudit.NodalIntegralChartTransition

open Polynomial

noncomputable section

universe u v
variable (R : Type u) [CommRing R]

def zEquation : Polynomial (Polynomial R) :=
  X ^ 2 - C (X ^ 2 * (X + 1))

def yEquation : Polynomial (Polynomial R) :=
  X - C (X ^ 2) * (C X + X)

abbrev zChart := AdjoinRoot (zEquation R)
abbrev yChart := AdjoinRoot (yEquation R)

def xZ : zChart R := AdjoinRoot.of (zEquation R) X
def yZ : zChart R := AdjoinRoot.root (zEquation R)
def xY : yChart R := AdjoinRoot.of (yEquation R) X
def zY : yChart R := AdjoinRoot.root (yEquation R)

theorem z_relation : yZ R ^ 2 = xZ R ^ 2 * (xZ R + 1) := by
  have h := AdjoinRoot.eval₂_root (zEquation R)
  simpa only [zEquation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_mul, map_pow,
    map_add, map_one, xZ, yZ, sub_eq_zero] using h

theorem y_relation : zY R = xY R ^ 2 * (xY R + zY R) := by
  have h := AdjoinRoot.eval₂_root (yEquation R)
  simpa only [yEquation, eval₂_sub, eval₂_mul, eval₂_add, eval₂_X, eval₂_C, map_pow,
    xY, zY, sub_eq_zero] using h

abbrev zOverlap := Localization.Away (yZ R)
abbrev yOverlap := Localization.Away (zY R)

def xZO : zOverlap R := algebraMap (zChart R) (zOverlap R) (xZ R)
def yZO : zOverlap R := algebraMap (zChart R) (zOverlap R) (yZ R)
def yZOinv : zOverlap R := IsLocalization.Away.invSelf (yZ R)
def xYO : yOverlap R := algebraMap (yChart R) (yOverlap R) (xY R)
def zYO : yOverlap R := algebraMap (yChart R) (yOverlap R) (zY R)
def zYOinv : yOverlap R := IsLocalization.Away.invSelf (zY R)

private theorem yZO_mul_inv : yZO R * yZOinv R = 1 :=
  IsLocalization.Away.mul_invSelf (yZ R)

private theorem zYO_mul_inv : zYO R * zYOinv R = 1 :=
  IsLocalization.Away.mul_invSelf (zY R)

private theorem zOverlap_relation : yZO R ^ 2 = xZO R ^ 2 * (xZO R + 1) := by
  simpa only [xZO, yZO, map_pow, map_mul, map_add, map_one] using
    congrArg (algebraMap (zChart R) (zOverlap R)) (z_relation R)

private theorem yOverlap_relation : zYO R = xYO R ^ 2 * (xYO R + zYO R) := by
  simpa only [xYO, zYO, map_pow, map_mul, map_add] using
    congrArg (algebraMap (yChart R) (yOverlap R)) (y_relation R)

private theorem zInY_vanishes :
    (zEquation R).eval₂ (Polynomial.aeval (xYO R * zYOinv R)).toRingHom
      (zYOinv R) = 0 := by
  simp only [zEquation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_pow, map_mul, map_add, map_one, Polynomial.aeval_X]
  linear_combination zYOinv R ^ 3 * yOverlap_relation R +
    zYOinv R ^ 2 * ((xYO R)^2 - 1) * zYO_mul_inv R

private theorem yInZ_vanishes :
    (yEquation R).eval₂ (Polynomial.aeval (xZO R * yZOinv R)).toRingHom
      (yZOinv R) = 0 := by
  simp only [yEquation, eval₂_sub, eval₂_mul, eval₂_add, eval₂_X, eval₂_C,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, Polynomial.aeval_X]
  linear_combination yZOinv R ^ 3 * zOverlap_relation R -
    yZOinv R * (yZO R * yZOinv R + 1) * yZO_mul_inv R

/-- The Z=1 coordinates expressed in the Y=1 chart with Z/Y inverted. -/
def zInY : zChart R →ₐ[R] yOverlap R :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval (xYO R * zYOinv R))
    (zYOinv R) (zInY_vanishes R)

/-- The Y=1 coordinates expressed in the Z=1 chart with Y/Z inverted. -/
def yInZ : yChart R →ₐ[R] zOverlap R :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval (xZO R * yZOinv R))
    (yZOinv R) (yInZ_vanishes R)

@[simp] theorem zInY_x : zInY R (xZ R) = xYO R * zYOinv R :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (Polynomial.aeval_X _)

@[simp] theorem zInY_y : zInY R (yZ R) = zYOinv R :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] theorem yInZ_x : yInZ R (xY R) = xZO R * yZOinv R :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (Polynomial.aeval_X _)

@[simp] theorem yInZ_z : yInZ R (zY R) = yZOinv R :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem unit_of_inv {S : Type v} [CommRing S] {a b : S} (h : a * b = 1) : IsUnit a :=
  ⟨⟨a, b, h, by simpa only [mul_comm] using h⟩, rfl⟩

private theorem zInY_unit : IsUnit (zInY R (yZ R)) := by
  rw [zInY_y]
  exact unit_of_inv ((mul_comm _ _).trans (zYO_mul_inv R))

private theorem yInZ_unit : IsUnit (yInZ R (zY R)) := by
  rw [yInZ_z]
  exact unit_of_inv ((mul_comm _ _).trans (yZO_mul_inv R))

def zToY : zOverlap R →ₐ[R] yOverlap R :=
  IsLocalization.Away.liftAlgHom (yZ R) (zInY_unit R)

def yToZ : yOverlap R →ₐ[R] zOverlap R :=
  IsLocalization.Away.liftAlgHom (zY R) (yInZ_unit R)

@[simp] theorem zToY_algebraMap (a : zChart R) :
    zToY R (algebraMap (zChart R) (zOverlap R) a) = zInY R a :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem yToZ_algebraMap (a : yChart R) :
    yToZ R (algebraMap (yChart R) (yOverlap R) a) = yInZ R a :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem zToY_inv : zToY R (yZOinv R) = zYO R := by
  have h := congrArg (fun a => zToY R a) (yZO_mul_inv R)
  simp only [map_mul, map_one, yZO, zToY_algebraMap, zInY_y] at h
  calc
    _ = zYO R * (zYOinv R * zToY R (yZOinv R)) := by
      rw [← mul_assoc, zYO_mul_inv, one_mul]
    _ = _ := by rw [h, mul_one]

@[simp] theorem yToZ_inv : yToZ R (zYOinv R) = yZO R := by
  have h := congrArg (fun a => yToZ R a) (zYO_mul_inv R)
  simp only [map_mul, map_one, zYO, yToZ_algebraMap, yInZ_z] at h
  calc
    _ = yZO R * (yZOinv R * yToZ R (zYOinv R)) := by
      rw [← mul_assoc, yZO_mul_inv, one_mul]
    _ = _ := by rw [h, mul_one]

private theorem chart_hom_ext {S : Type v} [CommRing S] [Algebra R S]
    {p : Polynomial (Polynomial R)} {f g : AdjoinRoot p →ₐ[R] S}
    (hx : f (AdjoinRoot.of p X) = g (AdjoinRoot.of p X))
    (hy : f (AdjoinRoot.root p) = g (AdjoinRoot.root p)) : f = g := by
  exact AdjoinRoot.algHom_ext' (Polynomial.algHom_ext hx) hy

private theorem z_section (a : zChart R) :
    yToZ R (zInY R a) = algebraMap (zChart R) (zOverlap R) a := by
  have h : (yToZ R).comp (zInY R) = IsScalarTower.toAlgHom R _ _ := by
    apply chart_hom_ext R
    · change yToZ R (zInY R (xZ R)) = xZO R
      simp only [zInY_x, map_mul, xYO, yToZ_algebraMap, yInZ_x, yToZ_inv]
      rw [mul_assoc, mul_comm (yZOinv R), yZO_mul_inv, mul_one]
    · change yToZ R (zInY R (yZ R)) = yZO R
      rw [zInY_y, yToZ_inv]
  exact DFunLike.congr_fun h a

private theorem y_section (a : yChart R) :
    zToY R (yInZ R a) = algebraMap (yChart R) (yOverlap R) a := by
  have h : (zToY R).comp (yInZ R) = IsScalarTower.toAlgHom R _ _ := by
    apply chart_hom_ext R
    · change zToY R (yInZ R (xY R)) = xYO R
      simp only [yInZ_x, map_mul, xZO, zToY_algebraMap, zInY_x, zToY_inv]
      rw [mul_assoc, mul_comm (zYOinv R), zYO_mul_inv, mul_one]
    · change zToY R (yInZ R (zY R)) = zYO R
      rw [yInZ_z, zToY_inv]
  exact DFunLike.congr_fun h a

/-- The actual two coordinate rings of the projective node's overlap are isomorphic. -/
def transition : zOverlap R ≃ₐ[R] yOverlap R := by
  refine AlgEquiv.ofAlgHom (zToY R) (yToZ R) ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (zY R))
    apply AlgHom.ext
    intro a
    change zToY R (yToZ R (algebraMap (yChart R) (yOverlap R) a)) = _
    rw [yToZ_algebraMap, y_section]
  · apply IsLocalization.algHom_ext (Submonoid.powers (yZ R))
    apply AlgHom.ext
    intro a
    change yToZ R (zToY R (algebraMap (zChart R) (zOverlap R) a)) = _
    rw [zToY_algebraMap, z_section]

end
end ManuscriptAudit.NodalIntegralChartTransition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalIntegralChartTransition.z_relation,
      ``ManuscriptAudit.NodalIntegralChartTransition.y_relation,
      ``ManuscriptAudit.NodalIntegralChartTransition.zToY_inv,
      ``ManuscriptAudit.NodalIntegralChartTransition.yToZ_inv,
      ``ManuscriptAudit.NodalIntegralChartTransition.transition] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
