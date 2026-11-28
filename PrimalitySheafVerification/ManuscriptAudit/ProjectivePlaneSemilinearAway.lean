import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProjectivePlaneSemilinear

/-! On every homogeneous open, the actual projective-plane semilinear
morphism is computed by the literal map of homogeneous fractions. -/

namespace ManuscriptAudit.ProjectivePlaneSemilinearAway

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspYChartAlgebra ProjectivePlaneSemilinear

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K L : Type u} [Field K] [Field L]
variable (e : K ≃+* L) (s : PlaneRing K) (t : PlaneRing L)
variable (h : coefficientMap e.toRingHom s = t)

/-- The literal semilinear map on a homogeneous localization whose
denominator has the prescribed image. -/
def mapAway : Away (grading K) s →+* Away (grading L) t := by
  subst t
  exact Away.map (coefficientMap e.toRingHom) s

variable {d : ℕ} (hs : s ∈ grading K d) (ht : t ∈ grading L d)

theorem mapAway_mk (n : ℕ) (x : PlaneRing K) (hx : x ∈ grading K (n • d)) :
    mapAway e s t h (Away.mk (grading K) hs n x hx) =
      Away.mk (grading L) ht n (coefficientMap e.toRingHom x) ((coefficientMap e.toRingHom).map_mem hx) := by
  subst t
  exact Away.map_mk (coefficientMap e.toRingHom) s hs n x hx

/-- The literal map on the homogeneous affine charts is the restriction
of the genuine semilinear morphism of the projective plane. -/
theorem awayι_planeIso (hd : 0 < d) :
    Proj.awayι (grading L) t ht hd ≫ (planeIso e).hom =
      Spec.map (CommRingCat.ofHom (mapAway e s t h)) ≫ Proj.awayι (grading K) s hs hd := by
  subst t
  exact Proj.awayι_comp_map (coefficientMap e.toRingHom) _ hd s hs

end

end ManuscriptAudit.ProjectivePlaneSemilinearAway

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProjectivePlaneSemilinearAway.awayι_planeIso
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
